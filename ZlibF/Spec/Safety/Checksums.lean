import ZlibF.Spec.Public.Checksums

/-!
# Checksums: one safety goal per checksum function

Step 2 of `docs/design/safety-functional-split.md`. A checksum call reads only its buffer and the
library's constant tables. Its safety goal says that on the documented domain the call returns
without a fault and leaves the heap exactly as it was: it writes nothing and allocates nothing.
Each can fail. The value is the subject of the functional goal of the same function
(`Goal.adler32`, `Goal.crc32`, ...).
-/

namespace ZlibF.Spec.Public
open C

/-- `uLong adler32(uLong adler, const Bytef *buf, uInt len)`.
**Safety of `adler32`**: on a readable buffer of `len` bytes, or `NULL` with `len = 0`
(`AdlerBufferBytes`; narrower than zlib.h, `docs/deviations.md`), the call returns and the heap
is unchanged. -/
def Goal.adler32_safety : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt32) (bytes : List UInt8),
    AdlerBufferBytes h pointer length.toNat bytes →
    ∃ value, C.run (Zlib.Adler32.adler32 seed pointer length) h = .ok (value, h)

/-- `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)`.
**Safety of `adler32_z`**: as `Goal.adler32_safety` with a 64-bit length. -/
def Goal.adler32_z_safety : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt64) (bytes : List UInt8),
    AdlerBufferBytes h pointer length.toNat bytes →
    ∃ value, C.run (Zlib.Adler32.adler32_z seed pointer length) h = .ok (value, h)

/-- `uLong adler32_combine(uLong adler1, uLong adler2, z_off_t len2)`.
**Safety of `adler32_combine`**: for every argument, also forged checksums and negative lengths,
the call returns and the heap is unchanged. -/
def Goal.adler32_combine_safety : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64),
    ∃ value, C.run (Zlib.Adler32.adler32_combine first second length) h = .ok (value, h)

/-- `uLong adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)`.
**Safety of `adler32_combine64`**: as `Goal.adler32_combine_safety`. -/
def Goal.adler32_combine64_safety : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64),
    ∃ value, C.run (Zlib.Adler32.adler32_combine64 first second length) h = .ok (value, h)

/-- `uLong crc32(uLong crc, const Bytef *buf, uInt len)`.
**Safety of `crc32`**: with the library's tables (`CrcGlobals`) and a readable buffer of `len`
bytes or `NULL` (`BufferBytes`), the call returns and the heap is unchanged. -/
def Goal.crc32_safety : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt32) (bytes : List UInt8),
    CrcGlobals h → BufferBytes h pointer length.toNat bytes →
    ∃ value, C.run (Zlib.Crc32.crc32 seed pointer length) h = .ok (value, h)

/-- `uLong crc32_z(uLong crc, const Bytef *buf, z_size_t len)`.
**Safety of `crc32_z`**: as `Goal.crc32_safety` with a 64-bit length. -/
def Goal.crc32_z_safety : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt64) (bytes : List UInt8),
    CrcGlobals h → BufferBytes h pointer length.toNat bytes →
    ∃ value, C.run (Zlib.Crc32.crc32_z seed pointer length) h = .ok (value, h)

/-- `uLong crc32_combine_gen(z_off_t len2)`.
**Safety of `crc32_combine_gen`**: for every length the call returns and the heap is unchanged. -/
def Goal.crc32_combine_gen_safety : Prop :=
  ∀ (h : Heap) (length : Int64), CrcGlobals h →
    ∃ value, C.run (Zlib.Crc32.crc32_combine_gen length) h = .ok (value, h)

/-- `uLong crc32_combine_gen64(z_off64_t len2)`.
**Safety of `crc32_combine_gen64`**: as `Goal.crc32_combine_gen_safety`. -/
def Goal.crc32_combine_gen64_safety : Prop :=
  ∀ (h : Heap) (length : Int64), CrcGlobals h →
    ∃ value, C.run (Zlib.Crc32.crc32_combine_gen64 length) h = .ok (value, h)

/-- `uLong crc32_combine_op(uLong crc1, uLong crc2, uLong op)`.
**Safety of `crc32_combine_op`**: for an operator `op` that `crc32_combine_gen` or
`crc32_combine_gen64` returned (zlib.h's domain), the call returns and the heap is unchanged. -/
def Goal.crc32_combine_op_safety : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64) (op : UInt64), CrcGlobals h →
    (C.run (Zlib.Crc32.crc32_combine_gen length) h = .ok (op, h) ∨
     C.run (Zlib.Crc32.crc32_combine_gen64 length) h = .ok (op, h)) →
    ∃ value, C.run (Zlib.Crc32.crc32_combine_op first second op) h = .ok (value, h)

/-- `uLong crc32_combine(uLong crc1, uLong crc2, z_off_t len2)`.
**Safety of `crc32_combine`**: for every argument the call returns and the heap is unchanged. -/
def Goal.crc32_combine_safety : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64), CrcGlobals h →
    ∃ value, C.run (Zlib.Crc32.crc32_combine first second length) h = .ok (value, h)

/-- `uLong crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)`.
**Safety of `crc32_combine64`**: as `Goal.crc32_combine_safety`. -/
def Goal.crc32_combine64_safety : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64), CrcGlobals h →
    ∃ value, C.run (Zlib.Crc32.crc32_combine64 first second length) h = .ok (value, h)

end ZlibF.Spec.Public
