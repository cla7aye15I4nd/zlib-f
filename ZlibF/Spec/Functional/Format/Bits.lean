/-!
# Format: bits, bytes and numbers

Heap-free, pointer-free vocabulary for the data format of `docs/spec/format/README.md`
(RFC 1950, 1951, 1952). Everything here is total and structurally recursive.

The reader functions return `none` when the input is too short. A reader that
succeeds returns the value and the bits that are left.
-/

namespace ZlibF.Spec

/-- The 8 bits of a byte, least significant bit first.
RFC 1951, 3.1.1 and `F-bit-order`: data elements are packed starting at the
least significant bit of each byte. -/
def byteBits (b : UInt8) : List Bool :=
  (List.range 8).map fun i => b.toNat.testBit i

/-- The bit sequence of a byte sequence, first bit first (`F-bit-order`). -/
def bytesToBits (bs : List UInt8) : List Bool :=
  bs.flatMap byteBits

/-- `readBits n inp` reads an `n`-bit number packed least significant bit first
(RFC 1951, 3.1.1; `F-bit-order`: lengths, extra bits, `HLIT`, `LEN`, ...).
It is NOT used for Huffman codes, which are packed most significant bit first. -/
def readBits : Nat → List Bool → Option (Nat × List Bool)
  | 0, inp => some (0, inp)
  | _ + 1, [] => none
  | n + 1, b :: r =>
    match readBits n r with
    | none => none
    | some (v, r') => some ((if b then 1 else 0) + 2 * v, r')

/-- `readBytes n inp` reads `n` whole bytes (8 bits each, least significant bit
first), as the body of a stored block (RFC 1951, 3.2.4). -/
def readBytes : Nat → List Bool → Option (List UInt8 × List Bool)
  | 0, inp => some ([], inp)
  | n + 1, inp =>
    match readBits 8 inp with
    | none => none
    | some (v, r) =>
      match readBytes n r with
      | none => none
      | some (bs, r') => some (v.toUInt8 :: bs, r')

/-- `readNats w n inp` reads `n` numbers of `w` bits each (least significant bit first). -/
def readNats (w : Nat) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, inp => some ([], inp)
  | n + 1, inp =>
    match readBits w inp with
    | none => none
    | some (v, r) =>
      match readNats w n r with
      | none => none
      | some (vs, r') => some (v :: vs, r')

/-- The `len`-bit representation of `v`, MOST significant bit first. This is the
order in which the bits of a Huffman code are read from the stream
(RFC 1951, 3.1.1; `F-bit-order`). -/
def natToBitsMSB (len v : Nat) : List Bool :=
  (List.range len).map fun i => v.testBit (len - 1 - i)

/-- Big-endian 4 bytes (zlib trailer and dictionary id, RFC 1950, 2.2). -/
def be32 (n : Nat) : List UInt8 :=
  [(n / 2 ^ 24 % 256).toUInt8, (n / 2 ^ 16 % 256).toUInt8, (n / 2 ^ 8 % 256).toUInt8, (n % 256).toUInt8]

/-- Little-endian 4 bytes (gzip trailer, RFC 1952, 2.3.1). -/
def le32 (n : Nat) : List UInt8 :=
  [(n % 256).toUInt8, (n / 2 ^ 8 % 256).toUInt8, (n / 2 ^ 16 % 256).toUInt8, (n / 2 ^ 24 % 256).toUInt8]

/-- Little-endian 2 bytes (gzip `XLEN` and header CRC, RFC 1952, 2.3.1). -/
def le16 (n : Nat) : List UInt8 :=
  [(n % 256).toUInt8, (n / 2 ^ 8 % 256).toUInt8]

end ZlibF.Spec
