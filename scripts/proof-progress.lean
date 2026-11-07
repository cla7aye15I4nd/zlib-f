import Lean

/-! Read-only progress export. This is a viewer input, not a verification gate. -/
open Lean

private def readNames (path : String) : IO (Array Name) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let names := lines.map String.trimAscii |>.map (·.toString) |>.filter
    (fun s => !s.isEmpty && !s.startsWith "#") |>.map String.toName
  if names.eraseDups != names then throw (IO.userError s!"duplicate registration in {path}")
  return names.toArray

private def sourcePath (env : Environment) (name : Name) : Option String := do
  let index ← env.getModuleIdxFor? name
  let moduleName := env.header.moduleNames[index]!
  if moduleName.getRoot != `ZlibF then none else
    let parts := moduleName.components.map fun p => match p with
      | .str _ s => s
      | .num _ n => toString n
      | .anonymous => ""
    some (String.intercalate "/" parts ++ ".lean")

private def axioms (env : Environment) (name : Name) : IO (Array Name) := do
  let context : Core.Context := { fileName := "<progress>", fileMap := default }
  let (result, _) ← Core.CoreM.toIO (collectAxioms name : CoreM (Array Name)) context { env := env }
  return result

private def refs (env : Environment) (expr : Expr) : Array String :=
  expr.getUsedConstants.filterMap fun n => if (sourcePath env n).isSome then some n.toString else none

def main (args : List String) : IO UInt32 := do
  let goals ← readNames (args.headD "tests/audit/goals.txt")
  let registered ← readNames (args[1]?.getD "tests/audit/theorems.txt")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
  let mut declarations : Array Json := #[]
  let mut proofMatches : Array (Name × Name) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some path := sourcePath env name | continue
    let isTheorem := match info with | .thmInfo _ => true | _ => false
    if isTheorem then
      if let .const target [] := info.type then
        if goals.contains target then proofMatches := proofMatches.push (target, name)
    declarations := declarations.push (Json.mkObj [
      ("name", toJson name.toString), ("source", toJson path),
      ("theorem", toJson isTheorem), ("registered", toJson (registered.contains name)), ("typeRefs", toJson (refs env info.type)),
      ("refs", toJson ((info.value? (allowOpaque := true)).map (refs env) |>.getD #[]))])
  let mut rows : Array Json := #[]
  for goal in goals do
    let some (.defnInfo info) := env.find? goal |
      throw (IO.userError s!"registered goal missing or not a definition: {goal}")
    if info.type != .sort .zero then throw (IO.userError s!"goal is not a closed Prop: {goal}")
    let mut proofs : Array Json := #[]
    for (_, name) in proofMatches.filter (·.1 == goal) do
      let used ← axioms env name
      let allowed := used.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n)
      proofs := proofs.push (Json.mkObj [
        ("name", toJson name.toString), ("source", toJson ((sourcePath env name).getD "")),
        ("registered", toJson (registered.contains name)), ("allowedAxioms", toJson allowed),
        ("axioms", toJson (used.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson goal.toString), ("source", toJson ((sourcePath env goal).getD "")),
      ("description", toJson ((← findDocString? env goal).getD "")), ("proofs", toJson proofs)])
  IO.println (Json.mkObj [("goals", toJson rows), ("declarations", toJson declarations)]).compress
  return 0
