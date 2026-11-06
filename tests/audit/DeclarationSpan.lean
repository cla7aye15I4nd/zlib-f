import Lean
open Lean

-- Source imports/commands are parsed, never elaborated. Offsets are UTF-8 bytes.
private def range (s : Syntax) : Except String (Nat × Nat) := do
  let some a := s.getPos? | throw "missing original start position"
  let some b := s.getTailPos? | throw "missing original end position"
  return (a.byteIdx, b.byteIdx)

private def rangeJson (s : Syntax) : Except String Json := do
  let (a, b) ← range s
  return Json.arr #[toJson a, toJson b]

private def errorIO {α : Type} (v : Except String α) : IO α :=
  match v with
  | .ok x => pure x
  | .error msg => throw (IO.userError msg)

private def declarationJson (s : Syntax) : Except String Json := do
  if s.getKind != ``Parser.Command.declaration then return Json.null
  if s.getNumArgs != 2 then throw "unexpected declaration AST shape"
  let decl := s[1]
  let kind := decl.getKind
  let named := kind == ``Parser.Command.definition || kind == ``Parser.Command.abbrev ||
    kind == ``Parser.Command.theorem || kind == ``Parser.Command.opaque
  if !named then return Json.null
  if decl.getNumArgs < 4 || decl[1].getKind != ``Parser.Command.declId then
    throw "unexpected named declaration AST shape"
  let id := decl[1][0]
  if !id.isIdent then throw "missing declaration identifier"
  let modifiers ← if s[0].getPos?.isSome then rangeJson s[0] else pure Json.null
  let mut fields := [
    ("syntaxName", toJson id.getId.toString),
    ("kind", toJson kind.toString),
    ("declaration", ← rangeJson s),
    ("modifiers", modifiers),
    ("identifier", ← rangeJson id)]
  -- A binder default may also contain :=. Use the value AST, never text search.
  let val := decl[3]
  if val.getKind == ``Parser.Command.declValSimple then
    if val.getNumArgs < 2 || !val[0].isAtom || val[0].getAtomVal != ":=" then
      throw "unexpected simple declaration-value shape"
    fields := fields ++ [
      ("assignment", ← rangeJson val[0]),
      ("body", ← rangeJson val[1]),
      ("valueWithSuffix", ← rangeJson val),
      ("supportedBody", toJson true)]
  else
    fields := fields ++ [("supportedBody", toJson false), ("valueKind", toJson val.getKind.toString)]
  return Json.mkObj fields

-- Reject every error-recovered AST. Fuel also bounds malformed-input iteration.
unsafe def main (args : List String) : IO UInt32 := do
  if args.length != 1 then
    IO.eprintln "usage: lean --run Span.lean SOURCE.lean"
    return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Lean}] {} 0 (loadExts := true)
  let path := args.head!
  let text ← IO.FS.readFile path
  if text.contains '\r' then throw (IO.userError "CR line endings unsupported; no spans accepted")
  let ctx := Parser.mkInputContext text path (normalizeLineEndings := false)
  let (_, initial, initialLog) ← Parser.parseHeader ctx
  if initialLog.hasErrors then throw (IO.userError "source header parse error")
  let mut state := initial
  let mut msgs := initialLog
  let mut commands : Array Json := #[]
  let mut finished := false
  for _ in [:text.utf8ByteSize + 1] do
    let (stx, next, log) := Parser.parseCommand ctx { env, options := {} } state msgs
    if log.hasErrors || next.recovering then
      for msg in log.toList do IO.eprintln (← msg.toString)
      throw (IO.userError "source command parse error; no spans accepted")
    if stx.getKind == ``Parser.Command.eoi then
      finished := true
      break
    if Parser.isTerminalCommand stx then
      throw (IO.userError "unexpected terminal command; no spans accepted")
    if next.pos ≤ state.pos then throw (IO.userError "parser did not advance")
    commands := commands.push <| Json.mkObj [
      ("kind", toJson stx.getKind.toString),
      ("span", ← errorIO (rangeJson stx)),
      ("declaration", ← errorIO (declarationJson stx))]
    state := next
    msgs := log
  if !finished then throw (IO.userError "parser fuel exhausted")
  IO.println <| (Json.mkObj [
    ("format", toJson "lean-command-spans-v1"),
    ("offsetUnit", toJson "utf8-bytes-half-open"),
    ("trustedImports", toJson #["Lean"]),
    ("sourceImportsExecuted", toJson false),
    ("byteLength", toJson text.utf8ByteSize),
    ("headerEnd", toJson initial.pos.byteIdx),
    ("commands", toJson commands)]).compress
  return 0
