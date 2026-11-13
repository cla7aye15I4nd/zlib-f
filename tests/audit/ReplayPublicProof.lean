import Lean
open Lean

def closure (original changed : Environment) (proof : Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut todo := #[proof]
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if result.contains name then continue
    let some info := changed.find? name <|> original.find? name |
      throw <| IO.userError s!"missing dependency {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"unsupported dependency {name}"
    if let .axiomInfo _ := info then
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throw <| IO.userError s!"unsupported axiom {name}"
    result := result.insert name info
    for dependency in info.getUsedConstantsAsSet do todo := todo.push dependency
    if let .inductInfo indInfo := info then
      for sibling in indInfo.all do
        todo := todo.push sibling
        let some (.inductInfo siblingInfo) := changed.find? sibling <|> original.find? sibling |
          throw <| IO.userError s!"missing inductive sibling {sibling}"
        todo := todo ++ siblingInfo.ctors.toArray
  return result

/-!
## Kernel replay with a bounded diagnostic

The same procedure as `Lean.Kernel.Environment.replay` (Lean.Replay): every constant of the
closure is sent to the kernel after the constants it uses; constructors and recursors are not
sent but compared with those the kernel generates for the replayed inductive types. The one
difference is the diagnostic. `Lean.Replay` renders a kernel exception with its full
expressions (`toMessageData`); for a proof term with much sharing that rendering can need far
more memory than the check itself. Here a kernel exception is reported by its kind, the
declaration and the head constant of the offending expression only, so a rejected replay stays
small. The kinds are the kernel's own message headings, so the accepted type failures are
classified exactly as before.
-/

namespace ReplayPublic

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- The head constant of an expression, for a bounded diagnostic. -/
def head (e : Expr) : String :=
  match e.getAppFn.constName? with
  | some n => s!" (head {n})"
  | none => ""

/-- The kernel's heading for an exception, without rendering any expression. -/
def describe : Kernel.Exception → String
  | .unknownConstant _ n => s!"unknown constant '{n}'"
  | .alreadyDeclared _ n => s!"constant has already been declared '{n}'"
  | .declTypeMismatch _ d _ => s!"declaration type mismatch {d.getTopLevelNames}"
  | .declHasMVars _ n _ => s!"declaration has metavariables '{n}'"
  | .declHasFVars _ n _ => s!"declaration has free variables '{n}'"
  | .funExpected _ _ e => s!"function expected{head e}"
  | .typeExpected _ _ e => s!"type expected{head e}"
  | .letTypeMismatch _ _ n _ _ => s!"let-declaration type mismatch '{n}'"
  | .exprTypeMismatch _ _ e _ => s!"type mismatch at{head e}"
  | .appTypeMismatch _ _ e _ _ => s!"application type mismatch{head e}"
  | .invalidProj _ _ e => s!"invalid projection{head e}"
  | .thmTypeIsNotProp _ n _ => s!"type of theorem '{n}' is not a proposition"
  | .other msg => (msg.take 400).toString
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory consumption detected"
  | .deepRecursion => "deep recursion detected"
  | .interrupted => "interrupted"

def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env }
  | .error ex => throw <| .userError s!"(kernel) {describe ex}"

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo info => addDecl (Declaration.defnDecl info)
        | .thmInfo info =>
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name && info.type == info'.type &&
                info.levelParams == info'.levelParams && info.all == info'.all then
              return
          addDecl (Declaration.thmDecl info)
        | .axiomInfo info => addDecl (Declaration.axiomDecl info)
        | .opaqueInfo info => addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponed : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"
  for rec in (← get).postponedRecursors do
    match (← get).env.find? rec, (← read).newConstants[rec]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {rec}"
    | _, _ => throw <| IO.userError s!"No such recursor {rec}"

def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) :
    IO Kernel.Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      checkPostponed
  return s.env

end ReplayPublic

unsafe def main (args : List String) : IO UInt32 := do
  let [originalDir, changedDir, moduleName, goalName, registry] := args |
    throw <| IO.userError "original lib, changed lib, source module, exact goal, registry required"
  initSearchPath (← findSysroot)
  let paths ← searchPathRef.get
  searchPathRef.set (System.FilePath.mk originalDir :: paths)
  let original ← importModules #[{module := `ZlibF}] {} 0
  searchPathRef.set (System.FilePath.mk changedDir :: paths)
  let changed ← importModules #[{module := moduleName.toName}] {} 0
  let names := (← IO.FS.readFile registry).splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  let candidates := names.filter fun name => match original.find? name with
    | some (.thmInfo info) => info.type == .const goalName.toName []
    | _ => false
  let proof :: _ := candidates | throw <| IO.userError "no registered exact public proof"
  if changed.contains proof then throw <| IO.userError "source module contains the designated proof"
  let constants ← closure original changed proof
  let fresh ← mkEmptyEnvironment
  try
    discard <| ReplayPublic.replay constants fresh.toKernelEnv
  catch error =>
    let message := error.toString
    -- Fail closed on resource, cancellation, malformed-artifact and unknown diagnostics.
    -- These are the kernel type-checking failures expected from the reviewed body edits.
    let typeFailure := ["\n(kernel) application type mismatch", "\n(kernel) declaration type mismatch",
      "\n(kernel) type mismatch"].any fun diagnostic => (message.splitOn diagnostic).length > 1
    unless message.startsWith "while replaying declaration '" &&
        typeFailure do
      throw error
    IO.println s!"EXACT_PROOF_REJECTED: {proof}: {error}"
    return 2
  IO.println s!"exact proof replayed: {proof}; {constants.size} dependencies"
  return 0
