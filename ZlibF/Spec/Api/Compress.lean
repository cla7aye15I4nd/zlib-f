import ZlibF.Spec.Api.Deflate

/-!
# API model: `compress`, `compress2`, `compressBound`, `uncompress`, `uncompress2`

The one-call utility functions of `compress.c` and `uncompr.c`, as relations between the source
bytes, the room in the destination, and the result. The data-only core records the bytes written.
`Compress2Z` separately records null checks, the stored length and the compatibility wrapper.
On an argument error, the stored length can remain the initial capacity although no bytes were written.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- `compressBound(sourceLen)` (`compress.c`): `n + (n >> 12) + (n >> 14) + (n >> 25) + 13`,
`2^64 - 1` on overflow (`uLong` is 64 bits). -/
def compressBound (n : Nat) : Nat :=
  let b := n + n / 2 ^ 12 + n / 2 ^ 14 + n / 2 ^ 25 + 13
  if b ≥ 2 ^ 64 then 2 ^ 64 - 1 else b

/-- The parameters that `compress2` gives `deflateInit`: zlib wrapper, 15 window bits,
`memLevel` 8, default strategy. -/
def compressParams (level : Int) : Option DeflParams :=
  deflInit? level 8 15 8 0

/-- `compress2(dest, &destLen, source, sourceLen, level)`: `cap` is `*destLen` on entry; the result
is the return code and the bytes written. `argsOK` is a coarse rejection flag
(`Z_STREAM_ERROR`). It does not describe all pointer shapes or the stored length; those are in
`Compress2Z` and `Compress2Wrapper`. `Z_MEM_ERROR` is an allocation failure.

* `Z_OK`: `dst` is a valid zlib stream of `src` of at most `cap` bytes.
* `Z_BUF_ERROR`: the room was used up (`|dst| = cap`) and was smaller than `compressBound`.
* `Z_STREAM_ERROR` (bad `level`, or null arguments) and `Z_MEM_ERROR`: nothing was written.
* In every case `|dst|` is at most `compressBound |src|` and, for `Z_OK`, a valid stream. -/
def Compress2 (argsOK : Bool) (level : Int) (src : List UInt8) (cap : Nat) (rc : Int)
    (dst : List UInt8) : Prop :=
  if argsOK = false then rc = Z.streamError ∧ dst = []
  else match compressParams level with
    | none => rc = Z.streamError ∧ dst = []
    | some p =>
      (rc = Z.memError ∧ dst = []) ∨
      (rc = Z.ok ∧ (DeflState.fresh p).Valid dst src ∧ dst.length ≤ cap ∧
        dst.length ≤ compressBound src.length) ∨
      (rc = Z.bufError ∧ dst.length = cap ∧ cap < compressBound src.length ∧
        ∃ out, (DeflState.fresh p).Valid out src ∧ dst <+: out)

/-- Pointer shape and input values at the `compress2_z` boundary. The source bytes are meaningful
only when the source is readable; a null source is valid exactly for an empty source. `capacity`
is the initial scalar value and is not read when `lengthNull` is true. Heap bounds, aliasing and
representable sizes belong to the concrete argument relation. -/
structure CompressCall where
  source : List UInt8
  capacity : Nat
  level : Int
  sourceNull : Bool
  destNull : Bool
  lengthNull : Bool

/-- Data returned by a compressor call. `storedLength` is the scalar value after the call, not
the number of bytes written on all error paths: argument rejection preserves the original
capacity. A missing scalar pointer is represented by `none`. -/
structure CompressResult where
  rc : Int
  produced : List UInt8
  storedLength : Option Nat

/-- The argument rejection that occurs before `*destLen = 0` or initialisation. A null
destination with zero capacity passes these checks and is refused by the inner `deflate`. -/
def CompressCall.rejected (c : CompressCall) : Prop :=
  (c.sourceNull = true ∧ c.source ≠ []) ∨ c.lengthNull = true ∨
    (c.destNull = true ∧ 0 < c.capacity)

instance (c : CompressCall) : Decidable c.rejected := by
  unfold CompressCall.rejected
  infer_instance

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen, int level)`.
The default LP64 entry-point contract, with null checks and error ordering. Argument rejection
leaves the scalar unchanged. A bad level is rejected before allocator failure can occur. A null
destination with zero capacity reaches initialisation: it can report `Z_MEM_ERROR`, otherwise
`Z_STREAM_ERROR`, and writes no bytes. With valid pointers, the data-only core `Compress2`
applies and the scalar is exactly the number of bytes written. No clause assumes a callee
contract; proving this relation for the concrete execution is a separate refinement theorem. -/
def Compress2Z (c : CompressCall) (r : CompressResult) : Prop :=
  if c.rejected then
    r.rc = Z.streamError ∧ r.produced = [] ∧
      r.storedLength = (if c.lengthNull then none else some c.capacity)
  else match compressParams c.level with
    | none => r.rc = Z.streamError ∧ r.produced = [] ∧ r.storedLength = some 0
    | some _ =>
      if c.destNull then
        (r.rc = Z.memError ∨ r.rc = Z.streamError) ∧ r.produced = [] ∧
          r.storedLength = some 0
      else Compress2 true c.level c.source c.capacity r.rc r.produced ∧
        r.storedLength = some r.produced.length

/-- `int compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)`.
The wrapper reads the scalar before the `_z` checks. Its defined-execution domain therefore
requires a nonnull readable and writable scalar pointer; `lengthNull = true` is a fault, not
a clean `Z_STREAM_ERROR`. The concrete execution definition preserves that fault. -/
def Compress2Wrapper (c : CompressCall) (r : CompressResult) : Prop :=
  c.lengthNull = false ∧ Compress2Z c r

/-- `compress(dest, &destLen, source, sourceLen)`: `compress2` with `Z_DEFAULT_COMPRESSION`. -/
def Compress (argsOK : Bool) (src : List UInt8) (cap : Nat) (rc : Int) (dst : List UInt8) : Prop :=
  Compress2 argsOK (-1) src cap rc dst

/-- `uncompress2(dest, &destLen, source, &sourceLen)`: `cap` is `*destLen`, `used` the new
`*sourceLen`. The stream is zlib, with a 15-bit window and no dictionary.

This legacy relation is not a reviewed implementation contract. Its empty-output clause on
memory failure is contradicted by a paired execution; see `docs/overview.md`. A proof about this
relation must not be presented as a refinement of `uncompress2`.

* `Z_OK`: the first `used` bytes of `src` are a complete zlib stream that decodes to `dst`,
  which fits in `cap`.
* `Z_BUF_ERROR`: `dst` filled the room (`|dst| = cap`) and is a proper prefix of the decoding of
  the stream that `src` begins.
* `Z_DATA_ERROR`: the input is corrupt or an incomplete stream, or it asks for a dictionary
  (`Z_NEED_DICT` becomes `Z_DATA_ERROR`).
* `Z_STREAM_ERROR` (null arguments, `argsOK` false), `Z_MEM_ERROR`: nothing was written.
* `dst` is always consistent with the input consumed (`Layer.Consistent`), `used ≤ |src|`.

Liveness: a source that begins with a complete stream (that needs no dictionary) whose decoding
fits in `cap` gives `Z_OK` and that decoding, unless memory fails; if the decoding does not fit,
the result is `Z_BUF_ERROR`. -/
def Uncompress2 (argsOK : Bool) (src : List UInt8) (cap : Nat) (rc : Int) (dst : List UInt8)
    (used : Nat) : Prop :=
  if argsOK = false then rc = Z.streamError ∧ dst = [] ∧ used = 0
  else
    used ≤ src.length ∧
    (rc = Z.ok ∨ rc = Z.bufError ∨ rc = Z.dataError ∨ rc = Z.memError) ∧
    (rc = Z.memError → dst = []) ∧
    (rc = Z.ok → Zlib.Decodes [] (src.take used) dst ∧ dst.length ≤ cap) ∧
    (rc = Z.bufError → dst.length = cap ∧ ∃ t o n, src.length ≤ n ∧ Zlib.Decodes [] ((src ++ t).take n) o ∧
      dst <+: o ∧ cap < o.length) ∧
    dst.length ≤ cap ∧
    (rc ≠ Z.memError → Layer.Consistent .zlib 15 [] (src.take used) dst ∨ rc = Z.dataError) ∧
    (∀ n o, Zlib.Decodes [] (src.take n) o → ¬ HdrNeedsDict .zlib 15 (src.take n) → o.length ≤ cap →
      rc = Z.ok ∨ rc = Z.memError) ∧
    (∀ n o, Zlib.Decodes [] (src.take n) o → ¬ HdrNeedsDict .zlib 15 (src.take n) → cap < o.length →
      rc = Z.bufError ∨ rc = Z.memError)

/-- `uncompress(dest, &destLen, source, sourceLen)`: `uncompress2` without the count of used
source bytes. -/
def Uncompress (argsOK : Bool) (src : List UInt8) (cap : Nat) (rc : Int) (dst : List UInt8) : Prop :=
  ∃ used, Uncompress2 argsOK src cap rc dst used

end ZlibF.Spec.Api
