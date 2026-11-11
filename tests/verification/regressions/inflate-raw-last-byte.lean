import ZlibF.Spec.Format.Huffman
import ZlibF.Spec.Format.Bits

open ZlibF.Spec

/-! `ConsumesWithinStream` said that a call that reads the last byte of a valid
stream returns `Z_STREAM_END` (or `Z_MEM_ERROR`). The raw stream below is one
fixed block with the six literals 200 to 205 (9-bit codes) and the end-of-block
code: 3 + 6 * 9 + 7 = 64 bits. The sixth literal ends at bit 57 of the last byte,
and the end-of-block code fills the rest of it. With room for five bytes,
inflate (windowBits -15) reads all eight bytes to decode the sixth literal, then
stops in `LIT` for want of room and returns `Z_OK`
(`tests/goals/inflate-meaning/raw-last-byte-no-room.c`). The clause now asks for a
trailer (not raw data), or room for the rest of the decoding and a flush other
than `Z_BLOCK` and `Z_TREES`. -/
namespace RawLastByteRegression

/-- The stream printed by the reproduction (deflate, level 9, `Z_FIXED`). -/
def stream : List UInt8 := [0x3b, 0x71, 0xf2, 0xd4, 0xe9, 0x33, 0x67, 0x01]

set_option maxRecDepth 100000 in
/-- Bits 48 to 56 are the code of the sixth literal: its last bit is in the last byte. -/
theorem sixth_literal :
    decodeSym fixedLitLens ((bytesToBits stream).drop 48) = some (205, (bytesToBits stream).drop 57) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Bits 57 to 63 are the end-of-block code: nothing is left after it. -/
theorem end_of_block : decodeSym fixedLitLens ((bytesToBits stream).drop 57) = some (256, []) := by
  decide +kernel

end RawLastByteRegression
