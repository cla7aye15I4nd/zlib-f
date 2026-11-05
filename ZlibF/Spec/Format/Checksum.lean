/-!
# Format: Adler-32 and CRC-32

Simple bytewise definitions (no tables). `docs/spec/format.md` section 5.
-/

namespace ZlibF.Spec

/-- One byte of Adler-32 (RFC 1950, 8.2): `s1 := (s1 + b) mod 65521`,
`s2 := (s2 + s1) mod 65521`, with the value `s2 * 65536 + s1`.
(lean-zip has an equivalent in `Zip.Adler32`.) -/
def adlerStep (a : UInt32) (b : UInt8) : UInt32 :=
  let s1 := (a.toNat % 65536 + b.toNat) % 65521
  let s2 := (a.toNat / 65536 + s1) % 65521
  UInt32.ofNat (s2 * 65536 + s1)

/-- `adler32Update a data` continues the Adler-32 value `a` over `data`
(the function `adler32(adler, buf, len)` of `zlib.h`). `F-adler-incremental`. -/
def adler32Update (a : UInt32) (data : List UInt8) : UInt32 :=
  data.foldl adlerStep a

/-- Adler-32 of a byte sequence (RFC 1950, 8.2): the start value is 1, so the empty sequence gives 1. -/
def adler32 (data : List UInt8) : UInt32 :=
  adler32Update 1 data

/-- The reflected CRC-32 polynomial of RFC 1952, 8.1.1.6.2. -/
def crcPoly : UInt32 := 0xEDB88320

/-- One bit step of the bit-reflected CRC: shift right, and xor the polynomial
if the bit shifted out was 1. -/
def crcBit (c : UInt32) : UInt32 :=
  if c &&& 1 = 1 then (c >>> 1) ^^^ crcPoly else c >>> 1

/-- One byte of the (already inverted) CRC register: xor the byte in, then 8 bit steps,
least significant bit first. -/
def crcByte (c : UInt32) (b : UInt8) : UInt32 :=
  (List.range 8).foldl (fun c _ => crcBit c) (c ^^^ b.toUInt32)

/-- `crc32Update crc data` continues the CRC-32 value `crc` over `data`
(the function `crc32(crc, buf, len)` of `zlib.h`): invert, process, invert
(RFC 1952, 8.1.1.6.2). `F-crc-incremental`. (lean-zip: `Zip.Crc32`.) -/
def crc32Update (crc : UInt32) (data : List UInt8) : UInt32 :=
  ~~~ (data.foldl crcByte (~~~ crc))

/-- CRC-32 of a byte sequence: the start value is 0, so the empty sequence gives 0. -/
def crc32 (data : List UInt8) : UInt32 :=
  crc32Update 0 data

/-- `F-adler-incremental`: feeding a sequence in pieces equals feeding it at once. -/
theorem adler32Update_append (a : UInt32) (x y : List UInt8) :
    adler32Update (adler32Update a x) y = adler32Update a (x ++ y) := by
  simp [adler32Update, List.foldl_append]

/-- `F-crc-incremental`: feeding a sequence in pieces equals feeding it at once. -/
theorem crc32Update_append (c : UInt32) (x y : List UInt8) :
    crc32Update (crc32Update c x) y = crc32Update c (x ++ y) := by
  simp [crc32Update, List.foldl_append]

end ZlibF.Spec
