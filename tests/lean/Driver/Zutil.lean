import ZlibF.Zlib.«zutil.c»
import DiffTest.Common

/-!
Lean side of the differential test for `zutil.c`. It calls the translation in
`ZlibF/Zlib/zutil.c.lean` (the module the proofs are about), nothing else.
-/

open DiffTest

/-- The text of a `const char *` result, read from the heap it points into. -/
def readStr (p : C.BPtr) : C.M String := do
  let n ← C.strlenB p
  let mut a : Array UInt8 := #[]
  for i in [0:n.toNat] do
    a := a.push (← C.index8 p i)
  pure (String.fromUTF8! (ByteArray.mk a))

def showStr (m : C.M String) : String :=
  match C.run m C.Heap.empty with
  | .ok (s, _) => s!"[{s}]"
  | .error f => showFault f

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "zlibVersion", [] => .ok (showStr (do readStr (← Zlib.Zutil.zlibVersion)))
  | "zlibCompileFlags", [] => .ok (showResult (C.run Zlib.Zutil.zlibCompileFlags C.Heap.empty))
  | "zError", [e] => do
    let n ← parseI64 e
    if n.toInt < -(2 ^ 31 : Int) || n.toInt ≥ 2 ^ 31 then throw "does not fit int"
    return showStr (do readStr (← Zlib.Zutil.zError (Int32.ofInt n.toInt)))
  | "zcalloc_free", [i, s] => do
    let items := UInt32.ofNat (← parseNat i)
    let size := UInt32.ofNat (← parseNat s)
    let m : C.M String := do
      let n := (items * size).toNat
      let p ← Zlib.Zutil.zcalloc .null items size
      if p == .null then return "null"
      let mut sum : UInt64 := 0
      for i in [0:n] do
        let q ← p.add i
        C.store8 q (UInt64.ofNat i * 31 + 7).toUInt8
      for i in [0:n] do
        let q ← p.add i
        sum := sum + (← C.load8 q).toUInt64
      Zlib.Zutil.zcfree .null p
      pure s!"{n} {sum}"
    return match C.run m C.Heap.empty with
      | .ok (s, _) => s
      | .error f => showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
