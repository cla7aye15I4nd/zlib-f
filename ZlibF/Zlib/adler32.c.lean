import ZlibF.Runtime.Reasoning

/-!
# adler32.c — faithful translation (draft)

Source: `zlib/adler32.c`, default build (`NO_DIVIDE` undefined, so
`MOD`/`MOD28` are `a %= BASE`), LP64. Translated statement by statement; the
`DO1`..`DO16` macros become `do1`/`do16` with the same expansion order.

Types: `uLong`/`unsigned long` = `UInt64`, `z_size_t` = `UInt64`,
`unsigned` = `UInt32`, `Bytef` = `UInt8`. Byte reads are promoted to `int`
and then converted to `unsigned long`, which preserves their value.

Status: translated by hand; not yet produced by a mechanical translator and not
yet differentially tested in this repository (see `docs/trusted-base.md`).
-/

namespace Zlib.Adler32
open C

def BASE : UInt64 := 65521
def NMAX : UInt64 := 5552

/-- Loop-carried locals of `adler32_z`. -/
structure Locals where
  adler : UInt64
  sum2 : UInt64
  buf : Ptr
  len : UInt64
  n : UInt32

/-- `DO1(buf,i)`: `{adler += (buf)[i]; sum2 += adler;}` -/
def do1 (s : Locals) (i : Int) : CM Locals := do
  let b ← index8 s.buf i
  let adler := s.adler + b.toUInt64
  pure { s with adler, sum2 := s.sum2 + adler }

/-- `DO16(buf)`: `DO8(buf,0); DO8(buf,8);`, i.e. `DO1(buf,0)` .. `DO1(buf,15)`. -/
def do16 (s : Locals) : CM Locals := do
  let s ← do1 s 0;  let s ← do1 s 1;  let s ← do1 s 2;  let s ← do1 s 3
  let s ← do1 s 4;  let s ← do1 s 5;  let s ← do1 s 6;  let s ← do1 s 7
  let s ← do1 s 8;  let s ← do1 s 9;  let s ← do1 s 10; let s ← do1 s 11
  let s ← do1 s 12; let s ← do1 s 13; let s ← do1 s 14; do1 s 15

/-- `adler += *buf++; sum2 += adler;` -/
def stepByte (s : Locals) : CM Locals := do
  let b ← load8 s.buf
  let buf ← s.buf.add 1
  let adler := s.adler + b.toUInt64
  pure { s with adler, buf, sum2 := s.sum2 + adler }

/-- `while (len--)` condition. -/
def lenPostDec (s : Locals) : CM (Bool × Locals) :=
  pure (s.len != 0, { s with len := s.len - 1 })

/-- `uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len)` -/
def adler32_z (adler : UInt64) (buf : Ptr) (len : UInt64) : CM UInt64 := do
  -- if (buf == Z_NULL) return 1L;   (upstream fix madler/zlib#1364, `patches/`)
  if buf == .null then return 1
  -- sum2 = (adler >> 16) & 0xffff; adler &= 0xffff;
  let sum2 := (adler >>> 16) &&& 0xffff
  let adler := adler &&& 0xffff
  -- if (len == 1) { ... }
  if len == 1 then
    let b ← index8 buf 0
    let mut adler := adler + b.toUInt64
    if adler >= BASE then adler := adler - BASE
    let mut sum2 := sum2 + adler
    if sum2 >= BASE then sum2 := sum2 - BASE
    return adler ||| (sum2 <<< 16)
  -- if (len < 16) { while (len--) {...} ... }
  if len < 16 then
    let s ← cwhile lenPostDec stepByte { adler, sum2, buf, len, n := 0 }
    let mut adler := s.adler
    if adler >= BASE then adler := adler - BASE
    let sum2 := s.sum2 % BASE  -- MOD28(sum2)
    return adler ||| (sum2 <<< 16)
  -- while (len >= NMAX) { ... }
  let s ← cwhile (fun s => pure (s.len >= NMAX, s))
    (fun s => do
      let s := { s with len := s.len - NMAX, n := (NMAX / 16).toUInt32 }
      -- do { DO16(buf); buf += 16; } while (--n);
      let s ← cdoWhile
        (fun s => do
          let s ← do16 s
          pure { s with buf := ← s.buf.add 16 })
        (fun s => let n := s.n - 1; pure (n != 0, { s with n }))
        s
      -- MOD(adler); MOD(sum2);
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE })
    { adler, sum2, buf, len, n := 0 }
  -- if (len) { ... }
  let s ← if s.len != 0 then do
      let s ← cwhile (fun s => pure (s.len >= 16, s))
        (fun s => do
          let s := { s with len := s.len - 16 }
          let s ← do16 s
          pure { s with buf := ← s.buf.add 16 })
        s
      let s ← cwhile lenPostDec stepByte s
      pure { s with adler := s.adler % BASE, sum2 := s.sum2 % BASE }
    else pure s
  return s.adler ||| (s.sum2 <<< 16)

/-- `uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len)` -/
def adler32 (adler : UInt64) (buf : Ptr) (len : UInt32) : CM UInt64 :=
  adler32_z adler buf len.toUInt64

/-- `local uLong adler32_combine_(uLong adler1, uLong adler2, z_off64_t len2)`
(`z_off64_t` = signed 64-bit `long` on LP64 Linux; `MOD63` is `%=` in the
default build). -/
def adler32_combine_ (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 := do
  -- if (len2 < 0) return 0xffffffffUL;
  if len2 < 0 then return 0xffffffff
  -- MOD63(len2);  i.e. len2 %= BASE (signed %, operands nonnegative here)
  let len2 := len2 % 65521
  -- rem = (unsigned)len2;
  -- signed -> unsigned conversion is modulo 2^32, i.e. reinterpret then truncate
  let rem : UInt32 := len2.toUInt64.toUInt32
  let sum1 := adler1 &&& (0xffff : UInt64)
  -- sum2 = rem * sum1;  (rem converted to unsigned long)
  let sum2 := rem.toUInt64 * sum1
  let sum2 := sum2 % BASE  -- MOD(sum2)
  let sum1 := sum1 + ((adler2 &&& (0xffff : UInt64)) + BASE - 1)
  let sum2 := sum2 + (((adler1 >>> 16) &&& (0xffff : UInt64)) + ((adler2 >>> 16) &&& (0xffff : UInt64)) + BASE - rem.toUInt64)
  let mut sum1 := sum1
  if sum1 >= BASE then sum1 := sum1 - BASE
  if sum1 >= BASE then sum1 := sum1 - BASE
  let mut sum2 := sum2
  if sum2 >= (BASE <<< 1) then sum2 := sum2 - (BASE <<< 1)
  if sum2 >= BASE then sum2 := sum2 - BASE
  return sum1 ||| (sum2 <<< 16)

/-- `uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2)` (`z_off_t` = `long`). -/
def adler32_combine (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 :=
  adler32_combine_ adler1 adler2 len2

/-- `uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)` -/
def adler32_combine64 (adler1 adler2 : UInt64) (len2 : Int64) : CM UInt64 :=
  adler32_combine_ adler1 adler2 len2

end Zlib.Adler32

/-!
# Adler-32 specification (RFC 1950 §8.2)

`spec lo hi bs`: starting from component sums `lo`, `hi` (each < 65521), feed
bytes `bs`; each byte updates `lo := (lo + b) mod 65521`, then
`hi := (hi + lo) mod 65521`. The checksum is `lo + 65536 * hi`.
This file is independent of the C translation.
-/

namespace Zlib.Adler32.Spec

def BASE : Nat := 65521

def step (st : Nat × Nat) (b : UInt8) : Nat × Nat :=
  ((st.1 + b.toNat) % BASE, (st.2 + (st.1 + b.toNat) % BASE) % BASE)

def sums (lo hi : Nat) (bs : List UInt8) : Nat × Nat := bs.foldl step (lo, hi)

/-- Adler-32 of `bs` continuing from the checksum value `adler`
(the conventional initial value is 1). -/
def adler32 (adler : Nat) (bs : List UInt8) : Nat :=
  let st := sums (adler % 65536 % BASE) (adler / 65536 % 65536 % BASE) bs
  st.1 + 65536 * st.2

end Zlib.Adler32.Spec


namespace Zlib.Adler32.Proofs
open C Zlib.Adler32

/-- Bytes `p .. p+n-1` of a block. -/
def seg (bytes : ByteArray) (p n : Nat) : List UInt8 := (List.range n).map (fun i => bytes[p + i]!)

end Zlib.Adler32.Proofs


/-! ## Main theorems

They state Theorems A1 (safety) and A2 (correctness) of `docs/proof/adler32.md`. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

/-- **Main theorem.** For every live block, offset and length that fits in the
block, and every initial value whose high component sum is canonical
(`< 65521`, true of any value adler32 itself returns), `adler32_z` runs
without undefined behavior, terminates, leaves the heap unchanged and returns
the Adler-32 of the bytes. -/
theorem adler32_z_correct (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (hvalid : (a >>> 16 &&& 65535).toNat < 65521) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  sorry

/-- For `len ≠ 1` the result is the Adler-32 for **every** initial value. -/
theorem adler32_z_correct_ne_one (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h1 : L ≠ 1) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  sorry

/-- **Safety.** For every initial value, `adler32_z` on an in-bounds buffer
terminates without undefined behavior and leaves the heap unchanged. -/
theorem adler32_z_safe (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) :
    ∃ r, C.run (adler32_z a (.ref blk off) L.toUInt64) h = .ok (r, h) := by
  sorry

end Zlib.Adler32.Proofs


/-! ## Theorems for `adler32_combine`, `adler32_combine64` and `adler32`

The combination theorem says that `adler32_combine64` of the checksums of `A` and `B`, with `len2` the length of `B`, is the checksum of `A ++ B`. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

variable {h : Heap}

/-- `adler32_combine_` never faults and leaves the heap unchanged. -/
theorem adler32_combine_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine_ a1 a2 len2) r := by
  sorry

/-- **Combination theorem.** For byte strings `A` and `B` (with `|B| < 2^63`),
`adler32_combine64(adler32(A), adler32(B), |B|) = adler32(A ++ B)`, where
`adler32` starts from the conventional initial value 1. -/
theorem adler32_combine_correct (A B : List UInt8) (hB : B.length < 2 ^ 63) :
    ∃ r, OkOn h (adler32_combine64 (Spec.adler32 1 A).toUInt64 (Spec.adler32 1 B).toUInt64
        (Int64.ofNat B.length)) r ∧ r.toNat = Spec.adler32 1 (A ++ B) := by
  sorry

/-- `adler32_combine64` is `adler32_combine_`: it never faults. -/
theorem adler32_combine64_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine64 a1 a2 len2) r := by
  sorry

/-- `adler32_combine` is `adler32_combine_`: it never faults. -/
theorem adler32_combine_c_safe (a1 a2 : UInt64) (len2 : Int64) :
    ∃ r, OkOn h (adler32_combine a1 a2 len2) r := by
  sorry

/-- `adler32` is `adler32_z` with a 32-bit length: it never faults on an in-bounds buffer. -/
theorem adler32_safe (h : Heap) (blk : Nat) (bytes : ByteArray)
    (hb : h.blocks[blk]? = some (some bytes)) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 32) :
    ∃ r, C.run (adler32 a (.ref blk off) L.toUInt32) h = .ok (r, h) := by
  sorry

end Zlib.Adler32.Proofs

