import ZlibF.Zlib.«crc32.c»
import DiffTest.Common

/-!
Lean side of the differential test for `crc32.c`. It calls the translation in
`ZlibF/Zlib/crc32.c.lean` (the module the proofs are about), nothing else.
Buffers: `null:<len>`, `hex:<digits>`, `off:<k>:<digits>` (the pointer is k bytes into the block).
-/

open DiffTest

/-- The heap of the test: nothing allocated, the static tables of `crc32.c` set. -/
def heap0 : C.Heap := { C.Heap.empty with static := Zlib.Crc32.initStatics default }

inductive B where
  | null (len : Nat)
  | bytes (off : Nat) (b : Array UInt8)

def parseB (s : String) : Except String B :=
  if s.startsWith "off:" then
    match (s.drop 4).toString.splitOn ":" with
    | [k, h] => do return .bytes (← parseNat k) (← parseHex h)
    | _ => throw s!"bad buffer {s}"
  else do
    match ← parseBuf s with
    | .null n => return .null n
    | .bytes b => return .bytes 0 b

def bufLen : B → Nat
  | .null n => n
  | .bytes _ b => b.size

def runBuf (b : B) (f : C.BPtr → C.M UInt64) : String :=
  showResult <| C.run (h := heap0) (do
    match b with
    | .null _ => f .null
    | .bytes off bs => do
      let p ← C.allocBytes (Array.replicate off 0 ++ bs)
      match p with
      | .ref r _ => f (.ref r off)
      | .null => f .null)

def showM (m : C.M UInt64) : String := showResult (C.run m heap0)

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "crc32_z", [a, b] => do
    let a ← parseU64 a
    let buf ← parseB b
    return runBuf buf fun p => Zlib.Crc32.crc32_z a p (UInt64.ofNat (bufLen buf))
  | "crc32", [a, b] => do
    let a ← parseU64 a
    let buf ← parseB b
    if bufLen buf ≥ 2 ^ 32 then throw "length does not fit uInt"
    return runBuf buf fun p => Zlib.Crc32.crc32 a p (UInt32.ofNat (bufLen buf))
  | "crc32_combine", [a1, a2, l] => do
    return showM (Zlib.Crc32.crc32_combine (← parseU64 a1) (← parseU64 a2) (← parseI64 l))
  | "crc32_combine64", [a1, a2, l] => do
    return showM (Zlib.Crc32.crc32_combine64 (← parseU64 a1) (← parseU64 a2) (← parseI64 l))
  | "crc32_combine_gen", [l] => do return showM (Zlib.Crc32.crc32_combine_gen (← parseI64 l))
  | "crc32_combine_gen64", [l] => do return showM (Zlib.Crc32.crc32_combine_gen64 (← parseI64 l))
  | "crc32_combine_op", [a1, a2, op] => do
    return showM (Zlib.Crc32.crc32_combine_op (← parseU64 a1) (← parseU64 a2) (← parseU64 op))
  | "get_crc_table", [] =>
    -- read the 256 entries through the returned pointer
    let m : C.M (Array UInt32) := do
      let p ← Zlib.Crc32.get_crc_table
      let mut a : Array UInt32 := #[]
      for i in [0:256] do
        a := a.push (← C.Ptr.index p i)
      pure a
    match C.run m heap0 with
    | .ok (a, _) => .ok (" ".intercalate (a.toList.map fun x => toString x.toNat))
    | .error f => .ok (showFault f)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
