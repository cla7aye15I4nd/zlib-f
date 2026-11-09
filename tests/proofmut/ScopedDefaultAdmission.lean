import Lean
import Lean.Replay
open Lean

namespace ScopedDefaultAdmission
-- Separate scoped test. The existing constant-Goal replay selector is unchanged.
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


def alpha : Expr → Expr
  | .app f a => .app (alpha f) (alpha a)
  | .lam _ d b bi => .lam .anonymous (alpha d) (alpha b) bi
  | .forallE _ d b bi => .forallE .anonymous (alpha d) (alpha b) bi
  | .letE _ t v b nd => .letE .anonymous (alpha t) (alpha v) (alpha b) nd
  | .mdata _ b => alpha b
  | .proj n i b => .proj n i (alpha b)
  | e => e


def closure (original changed : Environment) (roots replacements : Array Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut todo := roots
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if result.contains name then continue
    let some info := (if replacements.contains name then changed.find? name else original.find? name) |
      throw <| IO.userError s!"missing original dependency or permitted replacement {name}"
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
        let some (.inductInfo siblingInfo) := original.find? sibling |
          throw <| IO.userError s!"missing original inductive sibling {sibling}"
        todo := todo ++ siblingInfo.ctors.toArray
  return result


def proofName : Name := `Zlib.Deflate.Engine.Proofs.generic_default_public_contract
def functionName : Name := `Zlib.Deflate.deflate
def sourceName : Name := `Zlib.Deflate.Engine.Proofs.public_deflate_source
def operationName : Name := `Zlib.Deflate.Engine.Proofs.public_stream_guard_refusal

def declarationRecord (name : Name) (info : ConstantInfo) : Json :=
  Json.mkObj [("name",toJson name.toString),("type",typeSyntax info),
    ("semantic",declarationSyntax info),
    ("typeAlpha",toJson (reprStr (alpha info.type))),
    ("body",toJson (info.value? (allowOpaque := true) |>.map exprSyntax)),
    ("bodyAlpha",toJson (info.value? (allowOpaque := true) |>.map (fun v => reprStr (alpha v)))),
    ("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial)]

def main (args : List String) : IO UInt32 := do
  let [mode, originalDir, variantDir, registry, typePin, report] := args |
    throw <| IO.userError "mode originalLib variantLib originalRegistry verifiedTypePin report required"
  unless ["inspect", "inventory", "operation-seed", "baseline", "exact-mutant", "source-gate"].contains mode do
    throw <| IO.userError "unknown scoped admission mode"
  let registered := (← IO.FS.readFile registry).splitOn "\n" |>.map (fun s => s.trimAscii.toString)
  unless registered.contains proofName.toString do
    throw <| IO.userError "scoped target is absent from approved registry"
  initSearchPath (← findSysroot)
  let standard ← searchPathRef.get
  -- The runner clears inherited project search paths before invoking this tool.
  searchPathRef.set (System.FilePath.mk originalDir :: standard)
  let original ← importModules #[{module := `ZlibF.Proof.«deflate.c.default-public-contract»}] {} 0
  let some (.thmInfo root) := original.find? proofName |
    throw <| IO.userError "scoped registered target is not an original theorem"
  let rootType := typeSyntax (.thmInfo root)
  if mode == "inspect" then
    let constants ← closure original original #[proofName] #[]
    let mut semantic : Array Json := #[]
    for (name, ci) in constants.toList do
      let some index := original.getModuleIdxFor? name | continue
      let owner := original.header.moduleNames[index]!
      unless [ `Init, `Lean, `Std, `ZlibF ].contains owner.getRoot do
        throw <| IO.userError s!"unapproved dependency module {owner}"
      if owner.getRoot == `ZlibF then
        if let .thmInfo _ := ci then pure ()
        else semantic := semantic.push (Json.mkObj [("name",toJson name.toString),
          ("type",typeSyntax ci),("value",declarationSyntax ci)])
    IO.FS.writeFile report ((Json.mkObj [("type",rootType),
      ("proof",toJson proofName.toString),("semantic",toJson semantic)]).compress ++ "\n")
    return 0
  let expected ← match Json.parse (← IO.FS.readFile typePin) with
    | .ok value => pure value
    | .error msg => throw <| IO.userError msg
  unless expected == rootType do
    throw <| IO.userError "full original type differs from the externally verified approved lock pin"
  searchPathRef.set (System.FilePath.mk variantDir :: standard)
  let imports : Array Import := if mode == "operation-seed" then
    #[{module := `ZlibF.Proof.«deflate.c.engine.public-entry-refusal-source»}]
    else if mode == "inventory" || mode == "source-gate" then
    #[{module := `ZlibF.Proof.«deflate.c.engine.public-source»}]
    else #[{module := `ZlibF.Zlib.«deflate.c»}]
  let variant ← importModules imports {} 0
  if variant.contains proofName then
    throw <| IO.userError "variant source imports the selected target proof"
  let some (.defnInfo oldFn) := original.find? functionName | throw <| IO.userError "old function missing"
  let some (.defnInfo newFn) := variant.find? functionName | throw <| IO.userError "new function missing"
  unless oldFn.type.equal newFn.type && oldFn.levelParams == newFn.levelParams && oldFn.safety == newFn.safety do
    throw <| IO.userError "actual C function signature or safety changed"
  if mode == "operation-seed" then
    let some (.thmInfo oldOp) := original.find? operationName | throw <| IO.userError "original operational proof missing"
    let some (.thmInfo newOp) := variant.find? operationName | throw <| IO.userError "fresh positive operational proof missing"
    unless oldOp.levelParams == newOp.levelParams && (alpha oldOp.type).equal (alpha newOp.type) &&
        (alpha oldOp.value).equal (alpha newOp.value) do
      throw <| IO.userError "cached dependency seed differs from freshly compiled approved operational source"
    IO.FS.writeFile report ((Json.mkObj [("status",toJson "approved-operational-seed-bound"),
      ("alphaOnlyBinderNamesAndMdata",toJson true)]).compress ++ "\n")
    return 0
  if mode == "inventory" then
    let modules := #[`ZlibF.Zlib.«deflate.c», `ZlibF.Proof.«deflate.c.engine.public-source»]
    let mut sides : Array Json := #[]
    for env in #[original, variant] do
      let mut rows : Array Json := #[]
      for (name, ci) in env.constants.map₁.toList do
        let some index := env.getModuleIdxFor? name | continue
        if modules.contains env.header.moduleNames[index]! then
          rows := rows.push (declarationRecord name ci)
      sides := sides.push (toJson rows)
    IO.FS.writeFile report ((toJson sides).compress ++ "\n")
    return 0
  let mut roots := #[proofName]
  let mut replacements := if mode == "baseline" then #[] else #[functionName]
  if mode == "baseline" then
    unless oldFn.value.equal newFn.value do throw <| IO.userError "baseline body changed"
  else
    if oldFn.value.equal newFn.value then throw <| IO.userError "mutant body unchanged"
  if mode == "source-gate" then
    replacements := #[functionName, sourceName]
    roots := #[sourceName]
    let some operational := original.find? operationName | throw <| IO.userError "original operational lemma missing"
    for name in operational.getUsedConstantsAsSet do roots := roots.push name
  let constants ← closure original variant roots replacements
  if mode == "source-gate" && constants.contains operationName then
    throw <| IO.userError "source gate must exclude the original operational proof Expr"
  unless constants.contains functionName do
    throw <| IO.userError "actual function is outside the selected proof dependency closure"
  let fresh ← mkEmptyEnvironment
  try
    discard <| fresh.toKernelEnv.replay constants
  catch error =>
    let msg := error.toString
    let typeFailure := ["\n(kernel) application type mismatch", "\n(kernel) declaration type mismatch",
      "\n(kernel) type mismatch"].any (fun s => (msg.splitOn s).length > 1)
    unless mode == "exact-mutant" && msg.startsWith "while replaying declaration '" && typeFailure do
      throw error
    IO.FS.writeFile report ((Json.mkObj [("status",toJson "exact-scoped-proof-rejected"),
      ("proof",toJson proofName.toString),("diagnostic",toJson msg)]).compress ++ "\n")
    IO.println "EXACT_SCOPED_PROOF_REJECTED"
    return 2
  IO.FS.writeFile report ((Json.mkObj [("status",toJson "replayed"),("mode",toJson mode),
    ("constants",toJson constants.size),("overrides",toJson (replacements.map Name.toString))]).compress ++ "\n")
  return 0
end ScopedDefaultAdmission

def main (args : List String) : IO UInt32 := ScopedDefaultAdmission.main args
