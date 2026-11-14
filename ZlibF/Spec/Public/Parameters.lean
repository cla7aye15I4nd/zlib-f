/-!
# Parameter decoders

The return codes and flush values of `zlib.h` and the parameter checks of the `*Init2`/`*Reset2`
functions (computable, copied from `deflate.c` and `inflate.c`). Both the safety and the
functional goals use them; they moved here from `ZlibF/Spec/Functional/Api/Basic.lean`, unchanged
and in the same namespace, so that a safety goal does not import the API model
(`docs/design/safety-functional-split.md`).
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-! ## Return codes and flush values (`zlib.h`) -/

-- The return codes of `zlib.h`.
namespace Z
def ok : Int := 0
def streamEnd : Int := 1
def needDict : Int := 2
def errno : Int := -1
def streamError : Int := -2
def dataError : Int := -3
def memError : Int := -4
def bufError : Int := -5
def versionError : Int := -6
end Z

/-- The flush values of `zlib.h` (`Z_NO_FLUSH` .. `Z_TREES`); `partialFlush` is deflate only,
`trees` is inflate only. -/
inductive Flush where
  | noFlush | partialFlush | syncFlush | fullFlush | finish | block | trees
  deriving DecidableEq, Repr

/-- The integer value of a flush constant. -/
def Flush.code : Flush → Int
  | .noFlush => 0 | .partialFlush => 1 | .syncFlush => 2 | .fullFlush => 3
  | .finish => 4 | .block => 5 | .trees => 6

/-- `RANK` of `deflate.c`: the order used to refuse a repeated, useless flush. -/
def Flush.rank (f : Int) : Int := f * 2 - (if f > 4 then 9 else 0)

/-! ## Layers and window bits -/

/-- The wrapper an inflate stream expects: raw deflate (`windowBits < 0`), zlib, gzip, or
automatic detection of zlib or gzip (`windowBits >= 32`). -/
inductive Wrap where
  | raw | zlib | gzip | auto
  deriving DecidableEq, Repr

/-- `inflateInit2` / `inflateReset2` (inflate.c): the wrapper and the window bits (`0` means
"take it from the zlib header") selected by `windowBits`, or `none` for `Z_STREAM_ERROR`.
A gzip header with `windowBits = 0` uses 15 at run time, see `winBits`. -/
def inflWbits (w : Int) : Option (Wrap × Nat) :=
  if w < 0 then
    if w < -15 then none
    else if -w < 8 then none
    else some (.raw, (-w).toNat)
  else
    let wrap : Option Wrap :=
      if w / 16 = 0 then some .zlib else if w / 16 = 1 then some .gzip
      else if w / 16 = 2 then some .auto else none
    let wb : Int := if w < 48 then w % 16 else w
    match wrap with
    | none => none
    | some wr => if wb ≠ 0 ∧ (wb < 8 ∨ wb > 15) then none else some (wr, wb.toNat)

/-- The wrapper of a deflate stream. -/
inductive DWrap where
  | raw | zlib | gzip
  deriving DecidableEq, Repr

/-- The parameters fixed by `deflateInit2`; `level` is already `6` for `Z_DEFAULT_COMPRESSION`
and `wbits` is already `9` for `windowBits = 8` (zlib wrapper). -/
structure DeflParams where
  level : Nat
  wrap : DWrap
  wbits : Nat
  memLevel : Nat
  strategy : Nat
  deriving DecidableEq, Repr

/-- `deflateInit2_` (deflate.c) without the version and allocation checks: the parameters, or `none`
for `Z_STREAM_ERROR`. `method` must be `Z_DEFLATED = 8`. -/
def deflInit? (level method wbits memLevel strategy : Int) : Option DeflParams :=
  let level' : Int := if level = -1 then 6 else level
  let wrapWb : Option (DWrap × Int) :=
    if wbits < 0 then (if wbits < -15 then none else some (.raw, -wbits))
    else if wbits > 15 then some (.gzip, wbits - 16) else some (.zlib, wbits)
  match wrapWb with
  | none => none
  | some (wr, wb) =>
    if memLevel < 1 ∨ memLevel > 9 ∨ method ≠ 8 ∨ wb < 8 ∨ wb > 15 ∨ level' < 0 ∨ level' > 9 ∨
        strategy < 0 ∨ strategy > 4 ∨ (wb = 8 ∧ wr ≠ .zlib) then none
    else some ⟨level'.toNat, wr, (if wb = 8 then 9 else wb).toNat, memLevel.toNat, strategy.toNat⟩

/-- The input wrapper selected by the deflate wrapper. -/
def DWrap.toWrap : DWrap → Wrap
  | .raw => .raw | .zlib => .zlib | .gzip => .gzip

end ZlibF.Spec.Api
