import ZlibF.Spec.Api.Deflate

/-!
# API model: `compress`, `compress2`, `compressBound`, `uncompress`, `uncompress2`

The one-call utility functions of `compress.c` and `uncompr.c`, as relations between the source
bytes, the room in the destination, and the result. A destination is the list of bytes written
(`destLen` after the call is its length, on every return code, as in the code). The `*_z`
variants (`size_t` lengths) have the same specification, as the model has no `uInt` chunks.
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
is the return code and the bytes written. `argsOK` is false for the null-pointer cases
(`Z_STREAM_ERROR`). `Z_MEM_ERROR` is an allocation failure.

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

/-- `compress(dest, &destLen, source, sourceLen)`: `compress2` with `Z_DEFAULT_COMPRESSION`. -/
def Compress (argsOK : Bool) (src : List UInt8) (cap : Nat) (rc : Int) (dst : List UInt8) : Prop :=
  Compress2 argsOK (-1) src cap rc dst

/-- `uncompress2(dest, &destLen, source, &sourceLen)`: `cap` is `*destLen`, `used` the new
`*sourceLen`. The stream is zlib, with a 15-bit window and no dictionary.

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
