import ZlibF.Zlib.«inflate.c»
import ZlibF.Spec.Format.Wrapper
import ZlibF.Spec.Api.Basic

/-!
# inflate.c: stream-side fields of the format meaning (definitions)

The decoder fields that the wrapper stages of `ParseMeaning`
(`inflate.c.meaning`) fix: the configuration of a protocol trace, the width
and flags word chosen by the header, the per-mode position inside a zlib or
gzip header, and the bit buffer in the trailer. These definitions use only the
decoder record and byte lists, so `inflate.c.meaning` imports them and the
stream-side proofs can refine them here without editing the shared interface.

In a protocol trace no gzip header record is attached (`inflateGetHeader` is
not a trace step), so `head = NULL` and header capture never happens.

Statement test: `tests/goals/inflate-meaning` (state fields of the real
decoder against the parse position of the consumed input).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec
set_option autoImplicit false

/-- The value `inflateReset2` stores in `wrap` for a configured layer:
`0` raw, `(windowBits >> 4) + 5` otherwise. -/
def wrapCode : Api.Wrap → Int32
  | .raw => 0
  | .zlib => 5
  | .gzip => 6
  | .auto => 7

/-- Configuration fields that every state of a protocol trace keeps:
the wrapper code with the check bit set (no `inflateValidate`), the requested
wrapper and width of the initialization, no header record, and a configured
nonzero width as the decoder width. -/
def ConfigMatches (s : InflateState) (wrap : Api.Wrap) (configured : Nat) : Prop :=
  s.wrap = wrapCode wrap ∧ s.reqwrap = s.wrap ∧ s.head = none ∧
    s.reqbits.toNat = configured ∧ (configured ≠ 0 → s.wbits.toNat = configured)

/-- The header starts with the gzip magic. -/
abbrev IsGzipHeader (header : List UInt8) : Prop :=
  header.take 2 = [31, 139]

/-- The 16-bit word `FLAGS` stores for a gzip header: method and flags. -/
def gzipFlagsWord (header : List UInt8) : Int :=
  (header.getD 2 0).toNat + 256 * (header.getD 3 0).toNat

/-- The flags word after a complete wrapped header: `0` after a zlib header,
the method-and-flags word after a gzip header. `UPDATE_CHECK` and `LENGTH`
select CRC-32 and the length check by it. Raw data never reads it (`wrap = 0`
skips both). -/
def FlagsMatch (s : InflateState) (wrap : Api.Wrap) (header : List UInt8) : Prop :=
  if wrap = .raw then True
  else if IsGzipHeader header then s.flags.toInt = gzipFlagsWord header
  else s.flags = 0

/-- The width after a complete wrapper header: 8 to 15; with a configured
width of 0, the width a zlib header announces, or 15 for gzip. -/
def HeaderWidth (s : InflateState) (configured : Nat) (header : List UInt8) : Prop :=
  8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 ∧
    (configured = 0 →
      (IsGzipHeader header → s.wbits.toNat = 15) ∧
      (¬ IsGzipHeader header → 2 ^ s.wbits.toNat = Zlib.windowSize (header.headD 0)))

/-- Flag bit `k` of a gzip header (`FLG`, the fourth byte). -/
def gzipFlag (header : List UInt8) (k : Nat) : Prop :=
  (header.getD 3 0).toNat / 2 ^ k % 2 = 1

/-- The end of the optional extra field. -/
def gzipExtraEnd (header : List UInt8) : Nat :=
  if (header.getD 3 0).toNat / 4 % 2 = 1 then
    12 + ((header.getD 10 0).toNat + 256 * (header.getD 11 0).toNat)
  else 10

/-- The end of the optional name, once its terminating zero is read. -/
def gzipNameEnd (header : List UInt8) : Nat :=
  if (header.getD 3 0).toNat / 8 % 2 = 1 then
    gzipExtraEnd header + (header.drop (gzipExtraEnd header)).idxOf 0 + 1
  else gzipExtraEnd header

/-- The end of the optional comment, once its terminating zero is read. -/
def gzipCommentEnd (header : List UInt8) : Nat :=
  if (header.getD 3 0).toNat / 16 % 2 = 1 then
    gzipNameEnd header + (header.drop (gzipNameEnd header)).idxOf 0 + 1
  else gzipNameEnd header

/-- The position inside a gzip header that each mode stands for, with the
counter of the extra field and the bit buffer the mode expects. -/
def GzipPosition (s : InflateState) (bytes : List UInt8) : Prop :=
  (s.mode = TIME → bytes.length = 4 ∧ s.bits.toNat < 32) ∧
  (s.mode = OS → bytes.length = 8 ∧ s.bits.toNat < 16) ∧
  (s.mode = EXLEN → bytes.length = 10 ∧ s.bits.toNat < 16 ∧ (¬ gzipFlag bytes 2 → s.bits = 0)) ∧
  (s.mode = EXTRA → s.bits = 0 ∧
    (gzipFlag bytes 2 → 12 ≤ bytes.length ∧ bytes.length + s.length.toNat = gzipExtraEnd bytes) ∧
    (¬ gzipFlag bytes 2 → bytes.length = 10)) ∧
  (s.mode = NAME → s.bits = 0 ∧ gzipExtraEnd bytes ≤ bytes.length ∧
    (gzipFlag bytes 3 → 0 ∉ bytes.drop (gzipExtraEnd bytes)) ∧
    (¬ gzipFlag bytes 3 → bytes.length = gzipExtraEnd bytes)) ∧
  (s.mode = COMMENT → s.bits = 0 ∧ gzipNameEnd bytes ≤ bytes.length ∧
    (gzipFlag bytes 3 → 0 ∈ bytes.drop (gzipExtraEnd bytes)) ∧
    (gzipFlag bytes 4 → 0 ∉ bytes.drop (gzipNameEnd bytes)) ∧
    (¬ gzipFlag bytes 4 → bytes.length = gzipNameEnd bytes)) ∧
  (s.mode = HCRC → s.bits.toNat < 16 ∧ bytes.length = gzipCommentEnd bytes ∧
    (gzipFlag bytes 3 → 0 ∈ bytes.drop (gzipExtraEnd bytes)) ∧
    (gzipFlag bytes 4 → 0 ∈ bytes.drop (gzipNameEnd bytes)) ∧
    (¬ gzipFlag bytes 1 → s.bits = 0))

/-- The decoder inside a wrapper header after reading `bytes`.

* `HEAD`: nothing read, at most one byte held (raw data is
  always here before its first call).
* `DICTID`: the two zlib bytes read; the identifier is being collected.
* `FLAGS`: the gzip magic read; `check` is its CRC-32.
* `TIME` to `HCRC`: the flags word stored, `check` the CRC-32 of the header
  bytes when `FHCRC` is set, the mode at its position (`GzipPosition`). -/
def HeaderMatches (s : InflateState) (wrap : Api.Wrap) (configured : Nat)
    (bytes : List UInt8) : Prop :=
  (wrap = .raw → s.mode = HEAD) ∧
  (s.mode = HEAD → bytes = [] ∧ s.bits.toNat < 16) ∧
  (s.mode = DICTID → bytes.length = 2 ∧ ¬ IsGzipHeader bytes ∧ s.flags = 0 ∧
    s.bits.toNat < 32 ∧ HeaderWidth s configured bytes) ∧
  (s.mode = FLAGS → bytes = [31, 139] ∧ s.bits.toNat < 16 ∧
    s.check = (crc32 bytes).toUInt64 ∧ HeaderWidth s configured bytes) ∧
  (TIME ≤ s.mode → s.mode ≤ HCRC →
    IsGzipHeader bytes ∧ 4 ≤ bytes.length ∧ s.flags.toInt = gzipFlagsWord bytes ∧
    (gzipFlag bytes 1 → s.check = (crc32 bytes).toUInt64) ∧
    HeaderWidth s configured bytes ∧ GzipPosition s bytes)

/-- The DICTID field of a six-byte zlib header, as `check` holds it. -/
def dictId (header : List UInt8) : UInt64 :=
  UInt64.ofNat ((header.getD 2 0).toNat * 2 ^ 24 + (header.getD 3 0).toNat * 2 ^ 16 +
    (header.getD 4 0).toNat * 2 ^ 8 + (header.getD 5 0).toNat)

/-- The decoder in the trailer after reading `bytes` of it: `CHECK` before the
check value, `LENGTH` after the CRC-32 of a gzip trailer; whole bytes of the
next field are held. -/
def TrailerMatches (s : InflateState) (wrap : Api.Wrap) (header bytes : List UInt8) : Prop :=
  (s.mode = CHECK → bytes = []) ∧
  (s.mode = LENGTH → bytes.length = 4 ∧ wrap ≠ .raw ∧ IsGzipHeader header) ∧
  s.bits.toNat < 32

end Zlib.Inflate.Proofs
