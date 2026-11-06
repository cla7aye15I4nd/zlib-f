import ZlibF.Runtime.Alloc
import ZlibF.Zlib.«adler32.c»
import DiffTest.Heap

/-! Benchmark of the runtime, not a differential test: `n` stores into a byte block of `size` bytes, then the
number of bytes that changed. Memory and time are measured by the caller (`/usr/bin/time -v`). -/

open C

def storeLoop (p : BPtr) (size n : Nat) : M Unit := do
  let _ ← cwhile (fun (k : Nat) => pure (decide (k < n), k))
    (fun k => do
      let q ← Ptr.add p ((k * 7919 % size : Nat) : Int)
      store8 q (UInt8.ofNat (k % 251 + 1))
      pure (k + 1)) 0
  pure ()

/-- `adler32_z` and `crc32_z` over `size` bytes of a block (the checksums are printed). -/
def checksums (size : Nat) : IO UInt32 := do
  let data := Array.ofFn (n := size) fun i => UInt8.ofNat ((i.val * 31 + i.val / 7) % 256)
  let prog : M (UInt64 × UInt64) := do
    let p ← allocBytes data
    let a ← Zlib.Adler32.adler32_z 1 p (UInt64.ofNat size)
    let c ← Zlib.Crc32.crc32_z 0 p (UInt64.ofNat size)
    pure (a, c)
  match run prog DiffTest.fullHeap with
  | .ok ((a, c), _) => IO.println s!"adler32 {a} crc32 {c}"; return 0
  | .error _ => IO.println "fault"; return 1

def main (args : List String) : IO UInt32 := do
  if args.getD 0 "" == "checksums" then return ← checksums (args.getD 1 "1048576").toNat!
  let n := (args.getD 0 "1000000").toNat!
  let size := (args.getD 1 "65536").toNat!
  let prog : M Nat := do
    let p ← allocBytes (Array.replicate size 0)
    storeLoop p size n
    let mut cnt := 0
    for i in [0:size] do
      let v ← index8 p i
      if v != 0 then cnt := cnt + 1
    pure cnt
  match run prog Heap.empty with
  | .ok (c, _) => IO.println s!"changed bytes: {c}"; return 0
  | .error _ => IO.println "fault"; return 1
