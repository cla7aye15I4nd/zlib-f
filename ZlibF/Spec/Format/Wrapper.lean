import ZlibF.Spec.Format.Deflate
import ZlibF.Spec.Format.Checksum

/-!
# Format: the zlib and gzip wrappers

RFC 1950 and RFC 1952; the wrapper sections in `docs/spec/format/README.md`.
Both are exact: the whole `stream` is the wrapper, there are no bytes after the trailer.
-/

namespace ZlibF.Spec

/-- `F-zlib-header` (RFC 1950, 2.2): the compression method `CM = 8`, the window size field
`CINFO <= 7`, and `(CMF * 256 + FLG) mod 31 = 0`. -/
abbrev Zlib.HeaderOK (cmf flg : UInt8) : Prop :=
  cmf.toNat % 16 = 8 ∧ cmf.toNat / 16 ≤ 7 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0

/-- The window size `2^(CINFO + 8)` announced by `CMF` (RFC 1950, 2.2). -/
def Zlib.windowSize (cmf : UInt8) : Nat := 2 ^ (cmf.toNat / 16 + 8)

/-- A zlib stream (RFC 1950, 2.2) that decodes to `out`, given the dictionary `dict` that the
caller can supply (`[]` if none):
`CMF`, `FLG`, the optional `DICTID` (the Adler-32 of the dictionary, big-endian, present iff
`FDICT` = bit 5 of `FLG`), deflate data, and the big-endian Adler-32 of `out` (`F-zlib-check`).
When `FDICT` is set, back-references may reach into the dictionary; zlib keeps only the last
window-size bytes of it, so only those are used. The dictionary is ignored if `FDICT` is clear. -/
def Zlib.Decodes (dict stream out : List UInt8) : Prop :=
  ∃ (cmf flg : UInt8) (pre s : List UInt8),
    stream = cmf :: flg :: (pre ++ s) ∧ Zlib.HeaderOK cmf flg ∧
    (flg.toNat / 32 % 2 = 0 → pre = [] ∧
      Deflate.Prefix [] s (be32 (adler32 out).toNat) out) ∧
    (flg.toNat / 32 % 2 = 1 → pre = be32 (adler32 dict).toNat ∧
      Deflate.Prefix (dict.drop (dict.length - Zlib.windowSize cmf)) s (be32 (adler32 out).toNat) out)

/-- The gzip header of RFC 1952, 2.3, without the optional header CRC: `ID1 ID2` = 31, 139;
`CM` = 8; `FLG`; `MTIME` (4 bytes); `XFL`; `OS`; then, in this order, if `FEXTRA` (bit 2): `XLEN`
(2 bytes, little endian) and that many bytes; if `FNAME` (bit 3): the zero-terminated name; if
`FCOMMENT` (bit 4): the zero-terminated comment. -/
def Gzip.header (flg : UInt8) (mtime : List UInt8) (xfl os : UInt8)
    (extra name comment : List UInt8) : List UInt8 :=
  [31, 139, 8, flg] ++ mtime ++ [xfl, os] ++
    (if flg.toNat / 4 % 2 = 1 then le16 extra.length ++ extra else []) ++
    (if flg.toNat / 8 % 2 = 1 then name ++ [0] else []) ++
    (if flg.toNat / 16 % 2 = 1 then comment ++ [0] else [])

/-- A gzip member (RFC 1952, 2.3; format.md 4) that decodes to `out`: the header; if `FHCRC`
(bit 1) the low 16 bits of the CRC-32 of the header bytes before it, little endian; deflate data;
the little-endian CRC-32 of `out`; the little-endian length of `out` modulo `2^32`
(`F-gzip-check`). zlib requires the flag bits 5 to 7 to be 0. The values `extra`, `name`,
`comment` that belong to a flag that is clear are not used. -/
def Gzip.Decodes (stream out : List UInt8) : Prop :=
  ∃ (flg : UInt8) (mtime : List UInt8) (xfl os : UInt8) (extra name comment s : List UInt8),
    flg.toNat < 32 ∧ mtime.length = 4 ∧ extra.length < 2 ^ 16 ∧ 0 ∉ name ∧ 0 ∉ comment ∧
    stream = Gzip.header flg mtime xfl os extra name comment ++
        (if flg.toNat / 2 % 2 = 1 then
          le16 ((crc32 (Gzip.header flg mtime xfl os extra name comment)).toNat % 2 ^ 16) else []) ++ s ∧
    Deflate.Prefix [] s (le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)) out

/-- `F-flush-point` for the zlib layer: the zlib header (with `DICTID` when `FDICT` is set, as in
`Zlib.Decodes`), then deflate data that ends at a flush point and produces `out`. -/
def Zlib.Flushed (dict stream out : List UInt8) : Prop :=
  ∃ (cmf flg : UInt8) (pre s : List UInt8),
    stream = cmf :: flg :: (pre ++ s) ∧ Zlib.HeaderOK cmf flg ∧
    (flg.toNat / 32 % 2 = 0 → pre = [] ∧ Deflate.Flushed [] s out) ∧
    (flg.toNat / 32 % 2 = 1 → pre = be32 (adler32 dict).toNat ∧
      Deflate.Flushed (dict.drop (dict.length - Zlib.windowSize cmf)) s out)

/-- `F-flush-point` for the gzip layer: a gzip header (as in `Gzip.Decodes`), then deflate data
that ends at a flush point and produces `out`. -/
def Gzip.Flushed (stream out : List UInt8) : Prop :=
  ∃ (flg : UInt8) (mtime : List UInt8) (xfl os : UInt8) (extra name comment s : List UInt8),
    flg.toNat < 32 ∧ mtime.length = 4 ∧ extra.length < 2 ^ 16 ∧ 0 ∉ name ∧ 0 ∉ comment ∧
    stream = Gzip.header flg mtime xfl os extra name comment ++
        (if flg.toNat / 2 % 2 = 1 then
          le16 ((crc32 (Gzip.header flg mtime xfl os extra name comment)).toNat % 2 ^ 16) else []) ++ s ∧
    Deflate.Flushed [] s out

/-- `F-deflate-valid` for the zlib layer: `compressed` is a valid zlib stream for `input`
(given the preset dictionary `dict`, `[]` if none). -/
def Zlib.ValidWith (dict input compressed : List UInt8) : Prop :=
  Zlib.Decodes dict compressed input

/-- `F-deflate-valid` for the zlib layer without a dictionary. This is what `deflate` has
to produce. -/
def Zlib.Valid (input compressed : List UInt8) : Prop :=
  Zlib.Decodes [] compressed input

/-- `F-deflate-valid` for the gzip layer. -/
def Gzip.Valid (input compressed : List UInt8) : Prop :=
  Gzip.Decodes compressed input

end ZlibF.Spec
