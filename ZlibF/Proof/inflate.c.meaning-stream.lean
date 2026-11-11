import ZlibF.Zlib.«inflate.c»
import ZlibF.Spec.Format.Wrapper
import ZlibF.Spec.Api.Basic
import ZlibF.Math.«inflate-meaning-wrap»

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
wrapper and width of the initialization, no header record, a configured
nonzero width as the decoder width, and never `SYNC` (no `inflateSync`). -/
def ConfigMatches (s : InflateState) (wrap : Api.Wrap) (configured : Nat) : Prop :=
  s.wrap = wrapCode wrap ∧ s.reqwrap = s.wrap ∧ s.head = none ∧
    s.reqbits.toNat = configured ∧ (configured ≠ 0 → s.wbits.toNat = configured) ∧
    s.mode ≠ SYNC

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

/-- The position inside a gzip header that each mode stands for, as the
fields read so far (`ZlibF/Math/inflate-meaning-wrap`), with the counter of
the extra field and the bit buffer the mode expects. `flg` is the flags byte. -/
def GzipPosition (s : InflateState) (flg : UInt8) (bytes : List UInt8) : Prop :=
  (s.mode = TIME → bytes = [31, 139, 8, flg] ∧ s.bits.toNat ≤ 32) ∧
  (s.mode = OS → s.bits.toNat ≤ 16 ∧
    ∃ four, four.length = 4 ∧ bytes = [31, 139, 8, flg] ++ four) ∧
  (s.mode = EXLEN → s.bits.toNat ≤ 16 ∧ (flg.toNat / 4 % 2 = 0 → s.bits = 0) ∧
    ∃ six, six.length = 6 ∧ bytes = [31, 139, 8, flg] ++ six) ∧
  (s.mode = EXTRA → s.bits = 0 ∧ ∃ six, six.length = 6 ∧
    (flg.toNat / 4 % 2 = 1 → ∃ e, e.length + s.length.toNat < 2 ^ 16 ∧
      bytes = [31, 139, 8, flg] ++ six ++ le16 (e.length + s.length.toNat) ++ e) ∧
    (flg.toNat / 4 % 2 = 0 → bytes = [31, 139, 8, flg] ++ six)) ∧
  (s.mode = NAME → s.bits = 0 ∧ ∃ six ex part, six.length = 6 ∧ ex.length < 2 ^ 16 ∧
    (0 : UInt8) ∉ part ∧ (flg.toNat / 8 % 2 = 0 → part = []) ∧
    bytes = [31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ part) ∧
  (s.mode = COMMENT → s.bits = 0 ∧ ∃ six ex nm part, six.length = 6 ∧ ex.length < 2 ^ 16 ∧
    (0 : UInt8) ∉ nm ∧ (0 : UInt8) ∉ part ∧ (flg.toNat / 16 % 2 = 0 → part = []) ∧
    bytes = [31, 139, 8, flg] ++ six ++ gzipExtraPart flg ex ++ gzipNamePart flg nm ++ part) ∧
  (s.mode = HCRC → s.bits.toNat ≤ 16 ∧ (flg.toNat / 2 % 2 = 0 → s.bits = 0) ∧
    ∃ mt xfl os ex nm cm, GzipFields flg mt ex nm cm ∧
      bytes = Gzip.header flg mt xfl os ex nm cm)

/-- The decoder inside a wrapper header after reading `bytes`.

* `HEAD`: nothing read, at most one byte held, the width still 0 when the
  header chooses it (raw data is
  always here before its first call).
* `DICTID`: the two zlib bytes read; the identifier is being collected.
* `FLAGS`: the gzip magic read; `check` is its CRC-32.
* `TIME` to `HCRC`: the flags word stored, `check` the CRC-32 of the header
  bytes when `FHCRC` is set, the mode at its position (`GzipPosition`).
* A wrapped header has no dictionary and no window yet: `inflateReset`
  clears them, a wrapped stream installs a dictionary only in `DICT`, and no
  output has been written.
* No block has been read and no output counted (`last = 0`, `total = 0`). -/
def HeaderMatches (s : InflateState) (wrap : Api.Wrap) (configured : Nat)
    (bytes : List UInt8) : Prop :=
  (wrap = .raw → s.mode = HEAD) ∧
  (s.mode = HEAD → bytes = [] ∧ s.bits.toNat ≤ 16 ∧ (configured = 0 → s.wbits = 0)) ∧
  (s.mode = DICTID → bytes.length = 2 ∧ ¬ IsGzipHeader bytes ∧ s.flags = 0 ∧
    s.bits.toNat ≤ 32 ∧ HeaderWidth s configured bytes) ∧
  (s.mode = FLAGS → bytes = [31, 139] ∧ s.bits.toNat ≤ 16 ∧
    s.check = (crc32 bytes).toUInt64 ∧ HeaderWidth s configured bytes) ∧
  (TIME ≤ s.mode → s.mode ≤ HCRC →
    IsGzipHeader bytes ∧ 4 ≤ bytes.length ∧ s.flags.toInt = gzipFlagsWord bytes ∧
    ((bytes.getD 3 0).toNat / 2 % 2 = 1 → s.check = (crc32 bytes).toUInt64) ∧
    HeaderWidth s configured bytes ∧ GzipPosition s (bytes.getD 3 0) bytes) ∧
  (wrap ≠ .raw → s.havedict = 0 ∧ s.wsize = 0 ∧ s.whave = 0) ∧
  s.last = 0 ∧ s.total = 0

/-- The DICTID field of a six-byte zlib header, as `check` holds it. -/
def dictId (header : List UInt8) : UInt64 :=
  UInt64.ofNat ((header.getD 2 0).toNat * 2 ^ 24 + (header.getD 3 0).toNat * 2 ^ 16 +
    (header.getD 4 0).toNat * 2 ^ 8 + (header.getD 5 0).toNat)

/-- The decoder in the trailer after reading `bytes` of it: `CHECK` before the
check value, `LENGTH` after the CRC-32 of a gzip trailer; whole bytes of the
next field are held, at most the 32 bits `NEEDBITS` asks for. In `LENGTH`
`total` is the length of the whole output (`CHECK` has added this call's
output). -/
def TrailerMatches (s : InflateState) (wrap : Api.Wrap) (header out bytes : List UInt8) : Prop :=
  (s.mode = CHECK → bytes = []) ∧
  (s.mode = LENGTH → bytes.length = 4 ∧ wrap ≠ .raw ∧ IsGzipHeader header ∧
    s.total = UInt64.ofNat out.length) ∧
  s.bits.toNat ≤ 32

end Zlib.Inflate.Proofs
