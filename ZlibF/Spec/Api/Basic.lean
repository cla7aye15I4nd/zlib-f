import ZlibF.Spec.Format

/-!
# API model: vocabulary

Heap-free vocabulary for the model of the public API (`docs/design/api-model.md`): the return codes
and flush values of `zlib.h`, the parameter checks of the `*Init2`/`*Reset2` functions (computable,
copied from `deflate.c` and `inflate.c`), and the decoding oracle `Layer.Decodes` that the inflate
model uses. Nothing here mentions a heap or a pointer.
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

/-! ## The decoding oracle -/

/-- The window announced by a zlib header fits the window of the stream (`windowBits = 0`: any). -/
def ZlibFits (wbits : Nat) (s : List UInt8) : Prop :=
  wbits = 0 ∨ ∃ c, s.head? = some c ∧ c.toNat / 16 + 8 ≤ wbits

/-- `Layer.Decodes w wbits dict s o`: `s` is exactly one complete stream of layer `w` (with
configured window bits `wbits`) that decodes to `o` when the preset dictionary is `dict`.
This is the format specification, selected by the configuration. For raw streams only the last
`2^wbits` bytes of the dictionary are reachable.
Distances larger than the window are the one place where the format specification is
more permissive than zlib; see `FullWindow`. -/
def Layer.Decodes (w : Wrap) (wbits : Nat) (dict s o : List UInt8) : Prop :=
  match w with
  | .raw => Deflate.Decodes (dict.drop (dict.length - 2 ^ wbits)) s o
  | .zlib => Zlib.Decodes dict s o ∧ ZlibFits wbits s
  | .gzip => Gzip.Decodes s o
  | .auto => (Zlib.Decodes dict s o ∧ ZlibFits wbits s) ∨ Gzip.Decodes s o

/-- The configurations in which zlib accepts every stream that the format specification accepts:
the window is 32 KiB, which is the largest distance. This is `windowBits` 15 for every layer, and
`windowBits` 0 when the window is taken from the header (zlib: it must announce 15; gzip: zlib uses
15; auto: either). For a smaller window zlib may answer `Z_DATA_ERROR` for a valid stream with a
distance larger than the window (the check counts only the window and the output of the current
call, so it depends on how the caller splits the output; checked against the real library:
a gzip stream with `windowBits` 16 + 8 to 13 and an output room of 100 bytes per call fails); the
model then promises only "correct output or `Z_DATA_ERROR`". An empty prefix is full. -/
def FullWindow (w : Wrap) (wbits : Nat) (s : List UInt8) : Prop :=
  match w with
  | .raw => wbits = 15
  | .gzip => wbits = 0 ∨ wbits = 15
  | .zlib => wbits = 15 ∨ (wbits = 0 ∧ ∀ c, s.head? = some c → c.toNat / 16 + 8 = 15)
  | .auto => wbits = 15 ∨ (wbits = 0 ∧ (s.head? = some 31 ∨ ∀ c, s.head? = some c → c.toNat / 16 + 8 = 15))

/-- Legacy abstract detection parameter. Eight is refuted by a dynamic-table counterexample:
an impossible prefix of 230 bytes can be followed by a call that consumes 281 and returns OK.
This is not an established bound for actual inflate. A replacement requires a separate
source and format argument; the abstract rejection theorem alone cannot validate it. -/
def detectLag : Nat := 8

/-- The length of header that zlib needs before it can reject a stream: 2 bytes for a zlib header,
4 for a gzip header (magic, method and flags), none for raw deflate; 4 when the layer is detected. -/
def hdrLag : Wrap → Nat
  | .raw => 0 | .zlib => 2 | .gzip => 4 | .auto => 4

/-- `Viable`: `x` is the beginning of a stream that zlib has to accept: some stream of layer `w`
(possibly followed by other bytes) starts with `x`, or ends inside `x`. The first `hdrLag` bytes
are never rejected. -/
def Layer.Viable (w : Wrap) (wbits : Nat) (dict x : List UInt8) : Prop :=
  x.length < hdrLag w ∨ ∃ (t o : List UInt8) (n : Nat), Layer.Decodes w wbits dict ((x ++ t).take n) o

/-- `Detectable`: `x` has a prefix that is not viable and is at least `detectLag` bytes shorter
than `x`; a decoder that sees all of `x` and has room must answer `Z_DATA_ERROR`. -/
def Layer.Detectable (w : Wrap) (wbits : Nat) (dict x : List UInt8) : Prop :=
  ∃ m, m + detectLag ≤ x.length ∧ ¬ Layer.Viable w wbits dict (x.take m)

/-- The zlib header at the start of `x` asks for a dictionary (`FDICT`, bit 5 of `FLG`) and fits
the window; zlib then returns `Z_NEED_DICT` after reading the 6 bytes of header and `DICTID`. -/
def HdrNeedsDict (w : Wrap) (wbits : Nat) (x : List UInt8) : Prop :=
  (w = .zlib ∨ w = .auto) ∧ ∃ cmf flg r, x = cmf :: flg :: r ∧ Zlib.HeaderOK cmf flg ∧
    flg.toNat / 32 % 2 = 1 ∧ ZlibFits wbits x

end ZlibF.Spec.Api
