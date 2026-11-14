import ZlibF.Spec.Functional.Format
import ZlibF.Spec.Public.Parameters

/-!
# API model: vocabulary

Heap-free vocabulary for the model of the public API (`docs/design/api-model.md`): the return codes
and flush values of `zlib.h`, the parameter checks of the `*Init2`/`*Reset2` functions (computable,
copied from `deflate.c` and `inflate.c`), and the decoding oracle `Layer.Decodes` that the inflate
model uses. Nothing here mentions a heap or a pointer.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

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
