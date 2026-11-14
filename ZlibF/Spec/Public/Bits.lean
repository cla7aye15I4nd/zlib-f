/-!
# Bits of a byte sequence

`byteBits` and `bytesToBits`, moved unchanged from `ZlibF/Spec/Functional/Format/Bits.lean`
(`docs/design/safety-functional-split.md`): `PendingBits` in `Public/Streams.lean` uses them, and
a common module may not import the format model.
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

end ZlibF.Spec
