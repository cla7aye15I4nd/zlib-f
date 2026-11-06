import ZlibF.Runtime.Alloc

/-!
# adler32.c — faithful translation (draft)

Source: `zlib/adler32.c`, default build (`NO_DIVIDE` undefined, so
`MOD`/`MOD28` are `a %= BASE`), LP64. Translated statement by statement; the
`DO1`..`DO16` macros become `do1`/`do16` with the same expansion order.

Types: `uLong`/`unsigned long` = `UInt64`, `z_size_t` = `UInt64`,
`unsigned` = `UInt32`, `Bytef` = `UInt8`. Byte reads are promoted to `int`
and then converted to `unsigned long`, which preserves their value.

Status: translated by hand; differentially tested against the real C (`tests/`); the proofs are in
`ZlibF/Proof/adler32.c.lean`.
-/

namespace Zlib.Adler32
open C

def BASE : UInt64 := 65521
def NMAX : UInt64 := 5552

/-- Loop-carried locals of `adler32_z`. -/
structure Locals where
  adler : UInt64
  sum2 : UInt64
  buf : BPtr
  len : UInt64
  n : UInt32

/-- `DO1(buf,i)`: `{adler += (buf)[i]; sum2 += adler;}` -/
def do1 (s : Locals) (i : Int) : M Locals := do
  let b ← index8 s.buf i
  let adler := s.adler + b.toUInt64
  pure { s with adler, sum2 := s.sum2 + adler }

/-- `DO16(buf)`: `DO8(buf,0); DO8(buf,8);`, i.e. `DO1(buf,0)` .. `DO1(buf,15)`. -/
def do16 (s : Locals) : M Locals := do
  let s ← do1 s 0;  let s ← do1 s 1;  let s ← do1 s 2;  let s ← do1 s 3
  let s ← do1 s 4;  let s ← do1 s 5;  let s ← do1 s 6;  let s ← do1 s 7
  let s ← do1 s 8;  let s ← do1 s 9;  let s ← do1 s 10; let s ← do1 s 11
  let s ← do1 s 12; let s ← do1 s 13; let s ← do1 s 14; do1 s 15

/-- `adler += *buf++; sum2 += adler;` -/
def stepByte (s : Locals) : M Locals := do
  let b ← load8 s.buf
  let buf ← s.buf.add 1
  let adler := s.adler + b.toUInt64
  pure { s with adler, buf, sum2 := s.sum2 + adler }

/-- `while (len--)` condition. -/
def lenPostDec (s : Locals) : M (Bool × Locals) :=
  pure (s.len != 0, { s with len := s.len - 1 })

/-- `uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len)` -/
def adler32_z (adler : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
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
  -- initial Adler-32 value (deferred check for len == 1 speed)
  if buf == .null then return 1
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
def adler32 (adler : UInt64) (buf : BPtr) (len : UInt32) : M UInt64 :=
  adler32_z adler buf len.toUInt64

/-- `local uLong adler32_combine_(uLong adler1, uLong adler2, z_off64_t len2)`
(`z_off64_t` = signed 64-bit `long` on LP64 Linux; `MOD63` is `%=` in the
default build). -/
def adler32_combine_ (adler1 adler2 : UInt64) (len2 : Int64) : M UInt64 := do
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
def adler32_combine (adler1 adler2 : UInt64) (len2 : Int64) : M UInt64 :=
  adler32_combine_ adler1 adler2 len2

/-- `uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)` -/
def adler32_combine64 (adler1 adler2 : UInt64) (len2 : Int64) : M UInt64 :=
  adler32_combine_ adler1 adler2 len2

end Zlib.Adler32
