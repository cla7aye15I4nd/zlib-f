import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«trees.c»

open C

def patternBytes (n : Nat) : Array UInt8 :=
  Array.ofFn (n := n) fun i => UInt8.ofNat ((37 * i.val + 11) % 256)

def longestString : Nat :=
  (List.range strTable.size).foldl (fun best i =>
    if (strBytes (strTable.getD best "")).size < (strBytes (strTable.getD i "")).size
    then i else best) 0

def views : List (String × BRef) :=
  [("raw", .blk 0), ("str", .str longestString), ("str_empty", .str 0),
   ("dstate_depth", .dstate_depth 1), ("st_dist_code", .st_dist_code),
   ("st_length_code", .st_length_code)]

def fixtureHeap (layout : Nat) : Heap :=
  let h := Heap.empty
  let state := { DeflateState.garbage (fun _ => 0) with depth := patternBytes 573 }
  { h with
    bytes := upd h.bytes 0 (some (patternBytes 640))
    dstates := upd h.dstates 1 (some state)
    static := Zlib.Crc32.initStatics (Zlib.Trees.trees_statics h.static)
    nextBlk := 2
    byteBase := fun _ => ⟨layout % 8, Nat.mod_lt _ (by decide)⟩ }

def hexByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b.toNat / 16) '0', digits.getD (b.toNat % 16) '0']

def hexBytes (a : Array UInt8) : String :=
  String.join (a.toList.map hexByte)

def exportViews : IO UInt32 := do
  let h := fixtureHeap 0
  for (name, r) in views do
    match Space.get h r with
    | none => IO.eprintln s!"missing view {name}"; return 1
    | some data =>
      let id := if name == "str" then longestString else 0
      IO.println s!"DATA|{name}|{data.size}|{id}|{hexBytes data}"
  return 0

def runCases (path : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile path
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " " with
    | [fn, name, offText, lenText, seedText] =>
      let some (_, r) := views.find? (fun v => v.1 == name)
        | IO.eprintln s!"unknown view {name}"; return 1
      let some off := offText.toNat? | IO.eprintln "bad offset"; return 1
      let some len := lenText.toNat? | IO.eprintln "bad length"; return 1
      let some seed := seedText.toNat? | IO.eprintln "bad seed"; return 1
      if fn != "crc32" && fn != "crc32_z" then IO.eprintln "bad entry"; return 1
      let layouts := if name == "raw" then [0] else List.range 8
      for layout in layouts do
        let h := fixtureHeap layout
        let some data := Space.get h r | IO.eprintln "missing fixture"; return 1
        if data.size < off + len then IO.eprintln "invalid range"; return 1
        let p : BPtr := .ref r off
        let action := if fn == "crc32_z" then
            Zlib.Crc32.crc32_z (UInt64.ofNat seed) p (UInt64.ofNat len)
          else Zlib.Crc32.crc32 (UInt64.ofNat seed) p (UInt32.ofNat len)
        match C.run (Zlib.Crc32.addrOf p) h, C.run action h with
        | .ok (address, _), .ok (crc, after) =>
          let sameData := (Space.get after r : Option (Array UInt8)) == some data
          let sameBase := ByteAddress.base after r == ByteAddress.base h r
          IO.println s!"R|{fn}|{name}|{layout}|{off}|{len}|{seed}|{address.toNat % 8}|{crc.toNat}|{sameData}|{sameBase}"
        | .error _, _ => IO.eprintln s!"address fault {name}"; return 1
        | _, .error (.ub why) => IO.eprintln s!"CRC fault {name}: {why}"; return 1
        | _, .error .outOfFuel => IO.eprintln s!"CRC fuel {name}"; return 1
    | _ => IO.eprintln "bad case record"; return 1
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["export"] => exportViews
  | ["run", path] => runCases path
  | _ => IO.eprintln "expected export or run CASES"; return 2
