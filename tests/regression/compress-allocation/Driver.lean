import ZlibF.Zlib.«compress.c»
import ZlibF.Zlib.«uncompr.c»

/-!
# Differential-test Lean driver (paired with `driver.c`)

Calls the translations `Zlib.Compress.compress2_z`, `compress2`, `compress_z`,
`compress` and `Zlib.Uncompr.uncompress2_z` and prints exactly the rows that
`driver.c` prints, in the same order, in the same canonical format, for a
strict comparison by `compare.py`.

Caller buffers (destination, source and the scalar cells of `uncompress2_z`)
come from `C.allocBytes`, which is a harness operation: it takes no
allocation-oracle call, so `allocs=` counts the malloc attempts of the
translated function only, failed attempts included. The destination buffer is
filled with the same nonzero sentinel 0xA5 as the C side and its full contents
are printed, written bytes or not.

`live=` counts the live heap blocks of the final model heap beyond the
caller-owned blocks (the destination buffer, the source buffer when non-null,
and the two scalar cells for the `uncompress2_z` case).

The NULL-destLen calls of the uLongf wrappers `compress2`/`compress` are C
undefined behaviour; the Lean side raises `Fault.ub` and the row is printed
with the `UBROW` prefix and excluded from the defined-behaviour comparison.
Differential-test evidence only, not proof.
-/

namespace Regr
open C Zlib.Compress Zlib.Deflate Zlib.Uncompr Zlib.Gzguts

/-- The initial heap: every static table of the library installed. -/
def fullHeap : C.Heap :=
  { C.Heap.empty with static :=
      Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics C.Heap.empty.static)) }

/-- Arm the failure oracle: allocation attempt `sel` fails, all others succeed.
`none` fails nothing. -/
def arm (sel : Option Nat) : C.Heap :=
  { fullHeap with allocOk := fun n => sel.map (fun s => n != s) |>.getD true }

def SENT : UInt8 := 0xA5
def CAP : Nat := 64
def UCAP : Nat := 256

def hexByte (b : UInt8) : String :=
  String.push (String.push "" (Nat.digitChar (b.toNat / 16))) (Nat.digitChar (b.toNat % 16))

def hexOf (a : Array UInt8) : String := String.join (a.toList.map hexByte)

/-- The `n` bytes at `p`, read one by one. -/
def readBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    out := out.push (← index8 p i)
  return out

/-- The number of live blocks in the heap (some table holds an object). -/
def liveCount (h : C.Heap) (callerBlocks : Nat) : Nat :=
  (List.range h.nextBlk).countP fun b => callerBlocks ≤ b && h.slotUsed b

def fmtFail : Option Nat → String
  | none => "none"
  | some k => toString k

def fmtDl : Option UInt64 → String
  | none => "none"
  | some v => toString v.toNat

/-- One case of the matrix. -/
structure ZCase where
  name : String
  fn : String            -- compress2_z | compress2 | compress_z | compress
  fail : Option Nat
  destNull : Bool
  cap : UInt64
  src : Array UInt8
  srcNull : Bool
  level : Int32
  nullLen : Bool

def defLevel (fn : String) : Int32 :=
  if fn == "compress2_z" || fn == "compress2" then 6 else Z_DEFAULT_COMPRESSION

def runZCase (c : ZCase) : IO Unit := do
  let h0 := arm c.fail
  let body : C.M (Int32 × Option UInt64 × Array UInt8) := do
    -- caller buffers, no allocation-oracle call
    let dst ← C.allocBytes (Array.replicate CAP SENT)
    let sp ← if c.srcNull then pure (Ptr.null : BPtr) else C.allocBytes c.src
    let dptr := if c.destNull then (Ptr.null : BPtr) else dst
    let dlOpt : Option UInt64 := if c.nullLen then none else some c.cap
    let (rc, dl) ←
      if c.fn == "compress2_z" then
        let (r, d) ← compress2_z dptr dlOpt sp c.src.size.toUInt64 c.level
        pure (r, d)
      else if c.fn == "compress_z" then
        let (r, d) ← compress_z dptr dlOpt sp c.src.size.toUInt64
        pure (r, d)
      else if c.fn == "compress2" then
        -- the uLongf wrapper: a NULL destLen (dlOpt = none) is read first: C UB,
        -- the translation raises Fault.ub before producing a destLen
        let (r, d) ← compress2 dptr dlOpt sp c.src.size.toUInt64 c.level
        pure (r, some d)
      else
        let (r, d) ← compress dptr dlOpt sp c.src.size.toUInt64
        pure (r, some d)
    let out ← readBytes dst CAP
    pure (rc, dl, out)
  let callerBlocks : Nat := 1 + (if c.srcNull then 0 else 1)
  match C.run body h0 with
  | .ok ((rc, dl, out), h) =>
    let live := liveCount h callerBlocks
    IO.println s!"ROW case={c.name} fn={c.fn} fail={fmtFail c.fail} rc={rc.toInt} destLen={fmtDl dl} out={hexOf out} live={live} allocs={h.nalloc}"
  | .error f =>
    -- the only defined fault here is the NULL-destLen read of the wrappers (C UB)
    if c.nullLen && (c.fn == "compress2" || c.fn == "compress") then
      IO.println s!"UBROW case={c.name} fn={c.fn} fail={fmtFail c.fail} result=FAULT {repr f}"
    else
      IO.println s!"ROW case={c.name} fn={c.fn} fail={fmtFail c.fail} rc=FAULT destLen=none out=UNKNOWN live=UNKNOWN allocs=UNKNOWN"

/-- The `uncompress2_z` specification-review case: the five bytes
`[0x78,0x9c,0x73,0x04,0x00]`, capacity 256, malloc failure at attempt 1. -/
def uncCase : IO Unit := do
  let h0 := arm (some 1)
  let body : C.M (Int32 × UInt64 × UInt64 × Array UInt8) := do
    let dst ← C.allocBytes (Array.replicate UCAP SENT)
    let sp ← C.allocBytes #[0x78, 0x9c, 0x73, 0x04, 0x00]
    let dlc ← C.allocBytes (Array.replicate 8 0)
    let slc ← C.allocBytes (Array.replicate 8 0)
    store64 dlc 256
    store64 slc 5
    let rc ← uncompress2_z dst dlc sp slc
    let out ← readBytes dst UCAP
    let dl ← load64 dlc
    let sl ← load64 slc
    pure (rc, dl, sl, out)
  let callerBlocks : Nat := 4
  match C.run body h0 with
  | .ok ((rc, dl, sl, out), h) =>
    let live := liveCount h callerBlocks
    IO.println s!"UNCROW case=prefix5 fail=1 rc={rc.toInt} destLen={dl.toNat} sourceLen={sl.toNat} out={hexOf out} live={live} allocs={h.nalloc}"
  | .error f =>
    IO.println s!"UNCROW case=prefix5 fail=1 rc=FAULT destLen=UNKNOWN sourceLen=UNKNOWN out=UNKNOWN live=UNKNOWN allocs=UNKNOWN fault={repr f}"

def sweep : List (Option Nat) := [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6]

def one : Array UInt8 := #[0x61]

def main : IO Unit := do
  let fns := ["compress2_z", "compress2", "compress_z", "compress"]
  for fn in fns do
    let lvl := defLevel fn
    for f in sweep do
      runZCase { name := "normal", fn, fail := f, destNull := false, cap := 64,
                 src := one, srcNull := false, level := lvl, nullLen := false }
    for f in sweep do
      runZCase { name := "empty", fn, fail := f, destNull := false, cap := 64,
                 src := #[], srcNull := false, level := lvl, nullLen := false }
    runZCase { name := "nullsrc", fn, fail := none, destNull := false, cap := 64,
               src := one, srcNull := true, level := lvl, nullLen := false }
    runZCase { name := "nulldest_pos", fn, fail := none, destNull := true, cap := 64,
               src := one, srcNull := false, level := lvl, nullLen := false }
    for f in sweep do
      runZCase { name := "nulldest_zero", fn, fail := f, destNull := true, cap := 0,
                 src := one, srcNull := false, level := lvl, nullLen := false }
    if fn == "compress2_z" || fn == "compress2" then
      runZCase { name := "badlevel", fn, fail := none, destNull := false, cap := 64,
                 src := one, srcNull := false, level := 99, nullLen := false }
    if fn == "compress2_z" || fn == "compress_z" then
      runZCase { name := "nulllen", fn, fail := none, destNull := false, cap := 64,
                 src := one, srcNull := false, level := lvl, nullLen := true }
    else
      -- compress2/compress read *destLen first: C undefined behaviour.
      -- The Lean fault is printed (UBROW, excluded from the comparison
      -- matrix); the C witness runs separately under AddressSanitizer.
      runZCase { name := "nulllen", fn, fail := none, destNull := false, cap := 64,
                 src := one, srcNull := false, level := lvl, nullLen := true }
  uncCase

end Regr

/-- Entry point for `lean --run`. -/
def main : IO Unit := Regr.main
