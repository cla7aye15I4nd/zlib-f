import ZlibF.Runtime.Tables
import ZlibF.Zlib.gzfs

/-!
# gzguts.h — the header content of the gz* files

Default x86_64 Linux build (`STDC`, `STDC99`, `HAVE_VSNPRINTF`, `_LARGEFILE64_SOURCE` defined; `NO_GZCOMPRESS`,
`WIDECHAR`, `UNDER_CE`, `NO_snprintf`, `NO_vsnprintf` undefined). The constants `GZBUFSIZE`, `GZ_NONE`, `GZ_READ`,
`GZ_WRITE`, `GZ_APPEND`, `LOOK`, `GZIP`, the struct `gz_state` and `gzFile_s` come from the generated schema.
`COPY` of `gzguts.h` is `GZ_COPY` in the runtime (the name `COPY` is the inflate enumerator).

Decisions (see `docs/design/external-io.md`):

* `gzFile` is `GzFilePtr` (`some (.in_gzstate_x id)`), `gz_statep` is `GzStatePtr` (`some (.tab id)`); the cast
  `(gz_statep)file` is `castState`, `(gzFile)state` is `castFile`.
* `&(state->strm)` is `strmOf state`, computed without a dereference.
* Locals whose address is taken (`unsigned char buf[1]`) are blocks made by `allocLocal` (no allocation oracle:
  automatic storage cannot fail) and freed before every return.
* A pointer to a scalar (`int *errnum`, `z_size_t *destLen`) is a pointer to a byte block holding the value in
  little-endian order (`load32`, `store32`, `load64`, `store64`), because the runtime has no pointer to a single cell.
* Signed arithmetic is checked (`i64add`, `i64sub`, `i64neg`: overflow is `Fault.ub`).
-/

namespace Zlib.Gzguts
open C Zlib.GzFs

/-- `(gz_statep)file` -/
def castState (f : GzFilePtr) : GzStatePtr :=
  f.map fun | .in_gzstate_x i => .tab i

/-- `(gzFile)state` -/
def castFile (s : GzStatePtr) : GzFilePtr :=
  s.map fun | .tab i => .in_gzstate_x i

/-- `&(state->strm)` -/
def strmOf (s : GzStatePtr) : ZStreamPtr :=
  s.map fun | .tab i => .in_gzstate_strm i

/-- `*state` -/
def ldS (s : GzStatePtr) : M GzState := ldGzState s

/-- `*state = f(*state)`: a field write. -/
def updS (s : GzStatePtr) (f : GzState → GzState) : M Unit := do
  stGzState s (f (← ldGzState s))

/-- A field write of `state->x`. -/
def updX (s : GzStatePtr) (f : GzFile → GzFile) : M Unit :=
  updS s fun st => { st with x := f st.x }

/-- `*strm` -/
def ldZ (z : ZStreamPtr) : M ZStream := ldZStream z

/-- A field write of `*strm`. -/
def updZ (z : ZStreamPtr) (f : ZStream → ZStream) : M Unit := do
  stZStream z (f (← ldZStream z))

/-- Checked `z_off64_t` arithmetic: signed overflow is undefined. -/
def i64chk (r : Int) : M Int64 :=
  if -9223372036854775808 ≤ r ∧ r < 9223372036854775808 then pure (Int64.ofInt r) else C.ub "signed overflow (long)"
def i64add (a b : Int64) : M Int64 := i64chk (a.toInt + b.toInt)
def i64sub (a b : Int64) : M Int64 := i64chk (a.toInt - b.toInt)
def i64neg (a : Int64) : M Int64 := i64chk (-a.toInt)

/-- `(z_off64_t)u` for an unsigned 32-bit value. -/
def u32ToI64 (u : UInt32) : Int64 := Int64.ofNat u.toNat

/-- `GZ_OFF_MAX`: `((((z_off64_t)1 << (sizeof(z_off64_t) * CHAR_BIT - 2)) - 1) * 2 + 1)` -/
def GZ_OFF_MAX : Int64 := Int64.ofInt 9223372036854775807

/-- A local array: a fresh writable block with arbitrary content, outside the allocation oracle (automatic storage
cannot fail). Made by the runtime allocator `allocBytes`. -/
def allocLocal (n : Nat) : M BPtr := fun h =>
  allocBytes (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val)) h

/-- `*(int *)p` (the runtime has no pointer to a single `int`: see the file comment). -/
def load32 (p : BPtr) : M Int32 := do
  let b0 ← index8 p 0; let b1 ← index8 p 1; let b2 ← index8 p 2; let b3 ← index8 p 3
  return (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toInt32

/-- `*(int *)p = v` -/
def store32 (p : BPtr) (v : Int32) : M Unit := do
  let u := v.toUInt32
  store8 (← p.add 0) u.toUInt8
  store8 (← p.add 1) (u >>> 8).toUInt8
  store8 (← p.add 2) (u >>> 16).toUInt8
  store8 (← p.add 3) (u >>> 24).toUInt8

/-- `*(uint64_t *)p` -/
def load64 (p : BPtr) : M UInt64 := do
  let mut v : UInt64 := 0
  for i in [0:8] do
    v := v ||| ((← index8 p i).toUInt64 <<< (8 * i).toUInt64)
  return v

/-- `*(uint64_t *)p = v` -/
def store64 (p : BPtr) (v : UInt64) : M Unit := do
  for i in [0:8] do
    store8 (← p.add i) (v >>> (8 * i).toUInt64).toUInt8

/-- `memchr(p, c, n)`: reads at most `n` bytes and stops at the first match; faults if a byte it reads is outside
the object. Returns NULL if there is no match. -/
def memchrB (p : BPtr) (c : UInt8) (n : Nat) : M BPtr := do
  for i in [0:n] do
    if (← index8 p i) == c then return (← p.add i)
  return .null

end Zlib.Gzguts
