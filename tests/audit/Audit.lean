import Lean
open Lean

/-!
# Audit

Reads the compiled modules of `ZlibF` and reports on **every** declaration, not only on the listed
theorems. It never elaborates source and never runs code from the audited modules (no initialisers,
no syntax extensions), so the audited code cannot change what it reports.

Usage: `lake env lean --run tests/audit/Audit.lean <theorems.txt>`; the report goes to stdout, problems
make the exit code 1.

Report lines:
- `trusted <name> <hash of type> <hash of value>`: a definition, inductive type or structure that is
  not inside a `Proofs` namespace. These are the runtime, the translation, the specification and the
  invariants. A theorem statement is only as good as these, so they are locked (`tests/audit/trusted.lock`).
- `statement <name> :: <type>`: the exact type of a listed theorem (`tests/audit/statements.lock`).
- `goal <name> PROVED by <theorem>` or `goal <name> OPEN`: the target statements of the project are
  definitions of type `Prop` listed in `tests/audit/goals.txt` (so that no `sorry` is ever needed). A goal is
  PROVED only if a listed theorem has **exactly** the type `<name>`; a theorem with a weaker or different
  statement does not count. The report on goals is progress, not a lock: it changes whenever a goal is proved.
-/

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i]!).getRoot == `ZlibF
  | none => false

def inProofs (n : Name) : Bool := n.components.any (· == `Proofs)

def hex (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

def axiomsOf (env : Environment) (n : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default }
  let (a, _) ← Core.CoreM.toIO (collectAxioms n : CoreM (Array Name)) ctx { env := env }
  return a

def ppType (env : Environment) (ty : Expr) : IO String := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default }
  let (fmt, _, _) ← Meta.MetaM.toIO (Meta.ppExpr ty) ctx { env := env }
  return (fmt.pretty 110).replace "\n" " "

def readNames (path : String) : IO (List Name) := do
  if !(← System.FilePath.pathExists path) then return []
  return (← IO.FS.readFile path).splitOn "\n" |>.map (fun l => l.replace "\r" "")
    |>.filter (fun l => l != "" && !l.startsWith "#") |>.map String.toName

def main (args : List String) : IO UInt32 := do
  let thmFile := args.headD "tests/audit/theorems.txt"
  let goalFile := args.getD 1 "tests/audit/goals.txt"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
  let listed := (← IO.FS.readFile thmFile).splitOn "\n" |>.map (fun l => l.replace "\r" "")
    |>.filter (fun l => l != "" && !l.startsWith "#") |>.map String.toName
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let mut count := 0
  for (n, ci) in env.constants.map₁.toList do
    unless isOurs env n do continue
    count := count + 1
    -- 1. forbidden kinds of declaration
    -- compiler-generated auxiliary names (`_unsafe_rec`, `match_1`, ...) are not user declarations
    if !n.isInternal then
      if ci.isUnsafe then problems := problems.push s!"unsafe declaration {n}"
      if ci.isPartial then problems := problems.push s!"partial declaration {n}"
    match ci with
    | .axiomInfo _ => problems := problems.push s!"axiom {n}"
    | .opaqueInfo _ => problems := problems.push s!"opaque constant {n}"
    | _ => pure ()
    if (Compiler.getImplementedBy? env n).isSome then problems := problems.push s!"implemented_by on {n}"
    if isExtern env n then problems := problems.push s!"extern on {n}"
    -- 2. every definition and theorem: only the three standard axioms (so no `sorry`, no `native_decide`)
    if !n.isInternal then
      match ci with
      | .thmInfo _ | .defnInfo _ =>
        let bad := (← axiomsOf env n).filter (fun a => !allowedAxioms.contains a)
        unless bad.isEmpty do problems := problems.push s!"{n} depends on {bad}"
      | _ => pure ()
    -- 3. trusted declarations: everything that is not a theorem and not proof-side
    if !n.isInternal && !inProofs n then
      match ci with
      | .thmInfo _ => pure ()
      | _ =>
        let vh := match ci.value? with | some v => v.hash | none => 0
        lines := lines.push s!"trusted {n} {hex ci.type.hash} {hex vh}"
  -- 4. the listed theorems: they exist, are theorems, have a doc string, and their type is printed
  for n in listed do
    match env.find? n with
    | some (.thmInfo ti) =>
      if (← findDocString? env n).isNone then problems := problems.push s!"listed theorem {n} has no doc string"
      lines := lines.push s!"statement {n} :: {← ppType env ti.type}"
    | some _ => problems := problems.push s!"listed name {n} is not a theorem"
    | none => problems := problems.push s!"listed theorem {n} does not exist"
  -- 5. the goals: each is a definition of type `Prop`; it is proved by a listed theorem of exactly that type
  let goals ← readNames goalFile
  let mut proved := 0
  for g in goals do
    match env.find? g with
    | some (.defnInfo di) =>
      if di.type != .sort .zero then
        problems := problems.push s!"goal {g} is not a definition of type Prop"
      else
        let proof := listed.find? (fun t => match env.find? t with
          | some (.thmInfo ti) => ti.type == .const g []
          | _ => false)
        match proof with
        | some t => proved := proved + 1; lines := lines.push s!"goal {g} PROVED by {t}"
        | none => lines := lines.push s!"goal {g} OPEN"
    | some _ => problems := problems.push s!"goal {g} is not a definition"
    | none => problems := problems.push s!"goal {g} does not exist"
  IO.eprintln s!"{proved} of {goals.length} goals proved"
  for l in lines.qsort (· < ·) do IO.println l
  IO.eprintln s!"audited {count} declarations of ZlibF, {listed.length} listed theorems"
  for p in problems do IO.eprintln s!"PROBLEM: {p}"
  return if problems.isEmpty then 0 else 1
