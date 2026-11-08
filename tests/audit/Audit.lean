import Lean
open Lean

/-!
# Audit

Reads the compiled modules of `ZlibF` and reports on **every** declaration, not only on the listed
theorems. It never elaborates source and never runs code from the audited modules (no initialisers,
no syntax extensions), so the audited code cannot change what it reports.

Usage: `lake env lean --run tests/audit/Audit.lean <theorems.txt> <goals.txt> [--require-complete]`.
The `zlibf-audit` executable runs the same source. `--compare-axiom-collectors`
also checks each result against Lean's per-declaration collector for small fixtures.
Problems make the exit code 1. Strict mode also rejects every unproved goal.
Missing, empty and duplicate registries fail in both modes.

Report lines:
- `trusted <name> <hash of type> <hash of value>`: a definition, inductive type or structure that is
  part of the audited import closure, including private definitions and definitions in proof
  namespaces. These determine theorem meaning and are locked (`tests/audit/trusted.lock`).
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

def hex (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

-- The small Expr.hash values above are diagnostics, not collision-resistant locks.
-- Export the complete kernel syntax for SHA-256 hashing by the external gate.
def nameSyntax : Name → Json
  | .anonymous => toJson (0 : Nat)
  | .str parent text => toJson #[toJson (1 : Nat), nameSyntax parent, toJson text]
  | .num parent number => toJson #[toJson (2 : Nat), nameSyntax parent, toJson number]

def levelSyntax : Level → Json
  | .zero => toJson (0 : Nat)
  | .succ a => toJson #[toJson (1 : Nat), levelSyntax a]
  | .max a b => toJson #[toJson (2 : Nat), levelSyntax a, levelSyntax b]
  | .imax a b => toJson #[toJson (3 : Nat), levelSyntax a, levelSyntax b]
  | .param name => toJson #[toJson (4 : Nat), nameSyntax name]
  | .mvar id => toJson #[toJson (5 : Nat), nameSyntax id.name]

def exprSyntax : Expr → Json
  | .bvar i => toJson #[toJson (0 : Nat), toJson i]
  | .fvar id => toJson #[toJson (1 : Nat), nameSyntax id.name]
  | .mvar id => toJson #[toJson (2 : Nat), nameSyntax id.name]
  | .sort level => toJson #[toJson (3 : Nat), levelSyntax level]
  | .const name levels => toJson #[toJson (4 : Nat), nameSyntax name, toJson (levels.map levelSyntax)]
  | .app f a => toJson #[toJson (5 : Nat), exprSyntax f, exprSyntax a]
  | .lam name domain body info =>
      toJson #[toJson (6 : Nat), nameSyntax name, exprSyntax domain, exprSyntax body, toJson (reprStr info)]
  | .forallE name domain body info =>
      toJson #[toJson (7 : Nat), nameSyntax name, exprSyntax domain, exprSyntax body, toJson (reprStr info)]
  | .letE name type value body nondep =>
      toJson #[toJson (8 : Nat), nameSyntax name, exprSyntax type, exprSyntax value, exprSyntax body, toJson nondep]
  | .lit (.natVal n) => toJson #[toJson (9 : Nat), toJson n]
  | .lit (.strVal s) => toJson #[toJson (10 : Nat), toJson s]
  | .mdata _ body => exprSyntax body -- source metadata has no kernel meaning
  | .proj typeName field body => toJson #[toJson (11 : Nat), nameSyntax typeName, toJson field, exprSyntax body]

def declarationSyntax (ci : ConstantInfo) : Json :=
  match ci with
  | .defnInfo d => toJson #[toJson "definition", exprSyntax d.value, (match d.hints with | .opaque => toJson "opaque hint" | .abbrev => toJson "abbreviation" | .regular height => toJson height.toNat),
      toJson (reprStr d.safety)]
  | .inductInfo d => toJson #[toJson "inductive", toJson d.numParams, toJson d.numIndices,
      toJson (d.all.map nameSyntax), toJson (d.ctors.map nameSyntax), toJson d.numNested,
      toJson d.isRec, toJson d.isUnsafe, toJson d.isReflexive]
  | .ctorInfo d => toJson #[toJson "constructor", nameSyntax d.induct, toJson d.cidx,
      toJson d.numParams, toJson d.numFields, toJson d.isUnsafe]
  | .recInfo d => toJson #[toJson "recursor", toJson (d.all.map nameSyntax), toJson d.numParams,
      toJson d.numIndices, toJson d.numMotives, toJson d.numMinors, toJson d.k, toJson d.isUnsafe,
      toJson (d.rules.map fun r => toJson #[nameSyntax r.ctor, toJson r.nfields, exprSyntax r.rhs])]
  | .axiomInfo _ => toJson "rejected axiom"
  | .opaqueInfo _ => toJson "rejected opaque"
  | .quotInfo _ => toJson "quotient primitive"
  | .thmInfo _ => toJson "theorem proof omitted"

def typeSyntax (ci : ConstantInfo) : Json :=
  toJson #[toJson (ci.levelParams.map nameSyntax), exprSyntax ci.type]

def axiomsOf (env : Environment) (n : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default }
  let (a, _) ← Core.CoreM.toIO (collectAxioms n : CoreM (Array Name)) ctx { env := env }
  return a

-- Use the same dependency edges as Lean.collectAxioms, including types,
-- private bodies, constructors and axiom types. Build the complete graph
-- before propagation so mutual inductives cannot hide a dependency.
def axiomDependencies (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

def forbiddenAxioms (env : Environment) (roots : Array Name) : IO (NameMap NameSet) := do
  let env := env.setExporting false
  let mut pending := roots
  let mut visited : NameSet := {}
  let mut parents : NameMap (Array Name) := {}
  let mut propagate : Array (Name × Name) := #[]
  let mut next := 0
  while next < pending.size do
    let name := pending[next]!
    next := next + 1
    if visited.contains name then continue
    visited := visited.insert name
    let some ci := env.checked.get.find? name | continue
    if let .axiomInfo _ := ci then
      if !allowedAxioms.contains name then
        propagate := propagate.push (name, name)
    for dependency in axiomDependencies ci do
      parents := parents.insert dependency ((parents.find? dependency).getD #[] |>.push name)
      pending := pending.push dependency
  let mut result : NameMap NameSet := {}
  next := 0
  while next < propagate.size do
    let (name, axiomName) := propagate[next]!
    next := next + 1
    let known := (result.find? name).getD {}
    if known.contains axiomName then continue
    result := result.insert name (known.insert axiomName)
    for parent in (parents.find? name).getD #[] do
      propagate := propagate.push (parent, axiomName)
  return result

def ppType (env : Environment) (ty : Expr) : IO String := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default }
  let (fmt, _, _) ← Meta.MetaM.toIO (Meta.ppExpr ty) ctx { env := env }
  return (fmt.pretty 110).replace "\n" " "

def readNames (path : String) : IO (List Name) := do
  if !(← System.FilePath.pathExists path) then
    throw (IO.userError s!"missing registry: {path}")
  return (← IO.FS.readFile path).splitOn "\n" |>.map (fun l => l.replace "\r" "")
    |>.filter (fun l => l != "" && !l.startsWith "#") |>.map String.toName

def main (args : List String) : IO UInt32 := do
  let strict := args.contains "--require-complete"
  let compareAxioms := args.contains "--compare-axiom-collectors"
  let paths := args.filter (fun arg => arg != "--require-complete" && arg != "--compare-axiom-collectors")
  let thmFile := paths.headD "tests/audit/theorems.txt"
  let goalFile := paths.getD 1 "tests/audit/goals.txt"
  let compilerFile := paths.getD 2 "tests/audit/compiler-helpers.txt"
  let compilerHelpers ← readNames compilerFile
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
  let listed := (← IO.FS.readFile thmFile).splitOn "\n" |>.map (fun l => l.replace "\r" "")
    |>.filter (fun l => l != "" && !l.startsWith "#") |>.map String.toName
  let mut problems : Array String := #[]
  if listed.isEmpty then problems := problems.push "empty theorem registry"
  if listed.eraseDups.length != listed.length then
    problems := problems.push "duplicate theorem registration"
  let mut lines : Array String := #[]
  let mut count := 0
  let mut declarations : Array (Name × ConstantInfo) := #[]
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless isOurs env n do continue
    count := count + 1
    declarations := declarations.push (n, ci)
    -- 1. forbidden kinds of declaration
    -- Only the independently reviewed compiler auxiliaries are exempt. Private names and
    -- proof namespaces do not authorise unsupported declaration kinds or assumptions.
    if !compilerHelpers.contains n then
      if ci.isUnsafe then problems := problems.push s!"unsafe declaration {n}"
      if ci.isPartial then problems := problems.push s!"partial declaration {n}"
    match ci with
    | .axiomInfo _ => problems := problems.push s!"axiom {n}"
    | .opaqueInfo _ => problems := problems.push s!"opaque constant {n}"
    | _ => pure ()
    if (Compiler.getImplementedBy? env n).isSome then problems := problems.push s!"implemented_by on {n}"
    if isExtern env n then problems := problems.push s!"extern on {n}"
    -- Every definition and theorem remains a root, with the same reviewed exceptions.
    if !compilerHelpers.contains n then
      match ci with
      | .thmInfo _ | .defnInfo _ => roots := roots.push n
      | _ => pure ()
  -- A forbidden declaration kind already makes this closure invalid.
  -- Fixtures still exercise both collectors when parity is requested.
  if !problems.isEmpty && !compareAxioms then
    for p in problems do IO.eprintln s!"PROBLEM: {p}"
    return 1
  -- 2. Traverse shared dependencies once, then propagate every forbidden
  -- axiom to all its roots. The optional fixture check also runs Lean's
  -- original per-root collector; disagreement is itself a rejection.
  let dependencies ← forbiddenAxioms env roots
  for n in roots do
    let bad := ((dependencies.find? n).getD {}).toArray.qsort Name.lt
    if compareAxioms then
      let reference := (← axiomsOf env n).filter (fun a => !allowedAxioms.contains a)
      if bad != reference then
        problems := problems.push s!"axiom collector disagreement for {n}: {bad} != {reference}"
    unless bad.isEmpty do problems := problems.push s!"{n} depends on {bad}"
  -- An invalid declaration is already a failure. Do not serialize a full
  -- semantic report for a rejected import closure. No success path skips it.
  if !problems.isEmpty then
    for p in problems do IO.eprintln s!"PROBLEM: {p}"
    return 1
  for (n, ci) in declarations do
    -- 3. Every non-theorem definition is semantic, regardless of its namespace or visibility.
    -- Internal dependencies are included: a public definition may refer to a private helper.
    match ci with
    | .thmInfo _ => pure ()
    | _ =>
      let vh := match ci.value? with | some v => v.hash | none => 0
      lines := lines.push s!"trusted {n} {hex ci.type.hash} {hex vh}"
      lines := lines.push ("semantic " ++ (Json.mkObj [
        ("name", toJson n.toString), ("type", typeSyntax ci),
        ("value", declarationSyntax ci)]).compress)
  -- 4. the listed theorems: they exist, are theorems, have a doc string, and their type is printed
  for n in listed do
    match env.find? n with
    | some (.thmInfo ti) =>
      if (← findDocString? env n).isNone then problems := problems.push s!"listed theorem {n} has no doc string"
      lines := lines.push s!"statement {n} :: {← ppType env ti.type}"
      lines := lines.push ("theorem-type " ++ (Json.mkObj [
        ("name", toJson n.toString), ("type", typeSyntax (.thmInfo ti))]).compress)
    | some _ => problems := problems.push s!"listed name {n} is not a theorem"
    | none => problems := problems.push s!"listed theorem {n} does not exist"
  -- 5. Every standalone goal in the audited closure must be registered.
  let goals ← readNames goalFile
  for (n, ci) in env.constants.map₁.toList do
    if isOurs env n && n.components.contains `Goal then
      match ci with
      | .defnInfo di =>
        if di.type == .sort .zero && !goals.contains n then
          problems := problems.push s!"unregistered goal {n}"
      | _ => pure ()
  if goals.isEmpty then problems := problems.push "empty goal registry"
  if goals.eraseDups.length != goals.length then
    problems := problems.push "duplicate goal registration"
  let mut proved := 0
  for g in goals do
    match env.find? g with
    | some (.defnInfo di) =>
      lines := lines.push s!"target {g} {hex di.type.hash} {hex di.value.hash}"
      if di.type != .sort .zero then
        problems := problems.push s!"goal {g} is not a definition of type Prop"
      else
        let proof := listed.find? (fun t => match env.find? t with
          | some (.thmInfo ti) => ti.type == .const g []
          | _ => false)
        match proof with
        | some t => proved := proved + 1; lines := lines.push s!"goal {g} PROVED by {t}"
        | none =>
          lines := lines.push s!"goal {g} OPEN"
          if strict then problems := problems.push s!"unproved goal {g}"
    | some _ => problems := problems.push s!"goal {g} is not a definition"
    | none => problems := problems.push s!"goal {g} does not exist"
  IO.eprintln s!"{proved} of {goals.length} goals proved"
  for l in lines.qsort (· < ·) do IO.println l
  IO.eprintln s!"audited {count} declarations of ZlibF, {listed.length} listed theorems"
  for p in problems do IO.eprintln s!"PROBLEM: {p}"
  return if problems.isEmpty then 0 else 1
