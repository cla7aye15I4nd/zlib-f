import ZlibF.Spec.Api.Basic

/-!
# API model: the gzip header record (`gz_header`)

The part of `gz_header` that `deflateSetHeader` writes and `inflateGetHeader` reads
(`zlib.h`), as plain data. Pointers become `Option (List UInt8)` (`none` is `Z_NULL`).
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- `gz_header` as `deflateSetHeader` sees it: `extra`, `name`, `comment` are `none` for a null
pointer. `name` and `comment` hold no zero byte (they are zero-terminated strings) and `extra`
has fewer than `2^16` bytes. `xflags` is not used when writing. -/
structure GzHead where
  text : Bool
  time : Nat
  os : Nat
  extra : Option (List UInt8)
  name : Option (List UInt8)
  comment : Option (List UInt8)
  hcrc : Bool
  deriving DecidableEq, Repr

/-- The header record can be written (`deflateSetHeader` precondition of `zlib.h`). -/
def GzHead.Valid (h : GzHead) : Prop :=
  (∀ e, h.extra = some e → e.length < 2 ^ 16) ∧ (∀ s, h.name = some s → 0 ∉ s) ∧
    (∀ s, h.comment = some s → 0 ∉ s)

/-- The `OS_CODE` of the default x86_64 Linux build. -/
def osCode : Nat := 3

/-- The default header that `deflate` writes without `deflateSetHeader` (`deflate.c`): no flags,
`MTIME = 0`, `OS = OS_CODE`. -/
def GzHead.default : GzHead := ⟨false, 0, osCode, none, none, none, false⟩

/-- `XFL` written by `deflate` (`deflate.c`): 2 for level 9, 4 for the fastest algorithms
(level below 2, or Huffman only or run-length strategy), else 0. -/
def xflOf (p : DeflParams) : Nat :=
  if p.level = 9 then 2 else if p.strategy ≥ 2 ∨ p.level < 2 then 4 else 0

/-- The flag byte `FLG` of a header record. -/
def GzHead.flg (h : GzHead) : Nat :=
  (if h.text then 1 else 0) + (if h.hcrc then 2 else 0) + (if h.extra.isSome then 4 else 0) +
    (if h.name.isSome then 8 else 0) + (if h.comment.isSome then 16 else 0)

/-- The header without the optional header CRC, as `Gzip.header` of the format specification. -/
def GzHead.core (p : DeflParams) (h : GzHead) : List UInt8 :=
  Gzip.header h.flg.toUInt8 (le32 h.time) (xflOf p).toUInt8 h.os.toUInt8
    (h.extra.getD []) (h.name.getD []) (h.comment.getD [])

/-- The bytes that `deflate` writes before the deflate data: the header and, if `hcrc`, the low
16 bits of the CRC-32 of the header (RFC 1952). -/
def GzHead.bytes (p : DeflParams) (h : GzHead) : List UInt8 :=
  h.core p ++ (if h.hcrc then le16 ((crc32 (h.core p)).toNat % 2 ^ 16) else [])

/-- A gzip member with the given header bytes, that decodes to `out`: the header bytes, deflate
data, the little-endian CRC-32 and length of `out` (`Gzip.Decodes` with the header fixed). -/
def Gzip.DecodesWith (hdr stream out : List UInt8) : Prop :=
  ∃ s, stream = hdr ++ s ∧ Deflate.Prefix [] s (le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)) out

/-- What `inflateGetHeader` was given: whether `extra`, `name`, `comment` have a buffer and its
size (`extra_max`, `name_max`, `comm_max`). -/
structure HdrReq where
  extraMax : Option Nat
  nameMax : Option Nat
  commMax : Option Nat
  deriving DecidableEq, Repr

/-- The record after `inflate` has read the header (`done = 1`), or `done = -1` for a zlib
stream. `extraLen` is `extra_len`. -/
structure GzHdrOut where
  text : Bool
  time : Nat
  xflags : Nat
  os : Nat
  extra : Option (List UInt8)
  extraLen : Nat
  name : Option (List UInt8)
  comment : Option (List UInt8)
  hcrc : Bool
  done : Int
  deriving DecidableEq, Repr

/-- What `inflate` stores for a gzip header with the given fields (`A-header-fill`, `inflate.c`
cases `HEAD` to `HCRC`): `text`, `time`, `xflags`, `os`; `extra` truncated to `extra_max` and
`extra_len` the full length; the name and the comment including their zero terminator,
truncated to `name_max` and `comm_max`; a field that is absent in the stream, or that has no
buffer, is stored as `Z_NULL`; `hcrc` from the flag; `done = 1`. -/
def fillHeader (req : HdrReq) (flg : Nat) (mtime : Nat) (xfl os : Nat)
    (extra name comment : List UInt8) : GzHdrOut where
  text := flg % 2 = 1
  time := mtime
  xflags := xfl
  os := os
  extra := if flg / 4 % 2 = 1 then req.extraMax.map (fun m => extra.take m) else none
  extraLen := if flg / 4 % 2 = 1 then extra.length else 0
  name := if flg / 8 % 2 = 1 then req.nameMax.map (fun m => (name ++ [0]).take m) else none
  comment := if flg / 16 % 2 = 1 then req.commMax.map (fun m => (comment ++ [0]).take m) else none
  hcrc := flg / 2 % 2 = 1
  done := 1

/-- The header record is complete in the bytes `seen`: a valid gzip header (as written by
`Gzip.header`, with its header CRC if `FHCRC`) starts `seen`, and the record is `fillHeader` of its
fields. Used by the inflate model; for a zlib stream `done = -1`. -/
def HeaderRead (req : HdrReq) (seen : List UInt8) (h : GzHdrOut) : Prop :=
  (∃ (flg : UInt8) (mtime : List UInt8) (xfl os : UInt8) (extra name comment r : List UInt8),
    flg.toNat < 32 ∧ mtime.length = 4 ∧ extra.length < 2 ^ 16 ∧ 0 ∉ name ∧ 0 ∉ comment ∧
    seen = Gzip.header flg mtime xfl os extra name comment ++
        (if flg.toNat / 2 % 2 = 1 then
          le16 ((crc32 (Gzip.header flg mtime xfl os extra name comment)).toNat % 2 ^ 16) else []) ++ r ∧
    h = fillHeader req flg.toNat (mtime.foldr (fun b a => a * 256 + b.toNat) 0) xfl.toNat os.toNat
          extra name comment) ∨
  (∃ cmf flg r, seen = cmf :: flg :: r ∧ Zlib.HeaderOK cmf flg ∧ h.done = -1)

end ZlibF.Spec.Api
