import Lean
import Lean.Replay
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
    discard <| fresh.toKernelEnv.replay constants
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
