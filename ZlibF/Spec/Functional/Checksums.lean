import ZlibF.Spec.Public.Checksums
import ZlibF.Spec.Functional.Format.Checksum

/-!
# Checksums: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/Checksums.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

/-- Exact numeric behaviour, including the recorded noncanonical-seed caveat of the
one-byte fast path. Canonical seeds agree with the RFC checksum recurrence. -/
def adlerValue (seed : UInt64) (bytes : List UInt8) : UInt64 :=
  if bytes.length = 1 then
    let low := (seed.toNat % 65536 + (bytes.headD 0).toNat) % 65521
    let sum := seed.toNat / 65536 % 65536 + low
    UInt64.ofNat (low + 65536 * (if 65521 ≤ sum then sum - 65521 else sum))
  else (ZlibF.Spec.adler32Update (adlerStart seed) bytes).toUInt64

/-- Public update behaviour for either length width. All readable objects and all seeds are
covered; NULL queries require zero length and return one without reading bytes.
This explicit domain restriction is recorded in `docs/deviations.md`. The heap is unchanged. -/
def AdlerUpdate (program : UInt64 → BPtr → UInt64 → M UInt64) : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt64) (bytes : List UInt8),
    AdlerBufferBytes h pointer length.toNat bytes →
    C.run (program seed pointer length) h =
      .ok ((if pointer = .null then 1 else adlerValue seed bytes), h)

/-- `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)`.
NULL queries have zero length; nonnull readable objects cover 64-bit lengths and all seeds.
See `docs/deviations.md` for the query restriction. Exact value, no fault, termination,
no allocation and the complete heap frame. -/
def Goal.adler32_z : Prop := AdlerUpdate Zlib.Adler32.adler32_z

/-- `uLong adler32(uLong adler, const Bytef *buf, uInt len)`.
The public 32-bit length entry has the same buffer domain and exact result as `_z`.
NULL queries require zero length, as recorded in `docs/deviations.md`. -/
def Goal.adler32 : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt32) (bytes : List UInt8),
    AdlerBufferBytes h pointer length.toNat bytes →
    C.run (Zlib.Adler32.adler32 seed pointer length) h =
      .ok ((if pointer = .null then 1 else adlerValue seed bytes), h)

/-- Combine calls never fault or change the heap, even for forged checksums. Negative lengths
return the documented sentinel. For genuine checksums and the length of the second input,
the result is the checksum of concatenation. No claim of a meaningful checksum is made for
a forged pair that does not describe those inputs. -/
def AdlerCombine (program : UInt64 → UInt64 → Int64 → M UInt64) : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64), ∃ result,
    C.run (program first second length) h = .ok (result, h) ∧
    (length.toInt < 0 → result = 0xffffffff) ∧
    (∀ a b : List UInt8,
      first.toUInt32 = ZlibF.Spec.adler32 a → second.toUInt32 = ZlibF.Spec.adler32 b →
      length.toInt = (b.length : Int) → result = (ZlibF.Spec.adler32 (a ++ b)).toUInt64)

/-- `uLong adler32_combine(uLong adler1, uLong adler2, z_off_t len2)`.
Total execution, immutable heap, negative-length rejection and checksum concatenation. -/
def Goal.adler32_combine : Prop := AdlerCombine Zlib.Adler32.adler32_combine

/-- `uLong adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)`.
The LP64 64-bit-length entry has the same complete public combine contract. -/
def Goal.adler32_combine64 : Prop := AdlerCombine Zlib.Adler32.adler32_combine64

/-- Advancing a reflected CRC register through `bits` zero bits, as polynomial arithmetic.
This is independent of the implementation's tables and multiplication loop. -/
def crcAdvance (bits : Nat) (register : UInt32) : UInt32 :=
  (List.range bits).foldl (fun current _ => ZlibF.Spec.crcBit current) register

/-- The polynomial operator for a signed byte length; a negative length is rejected with zero. -/
def crcOperator (length : Int64) : UInt64 :=
  if length.toInt < 0 then 0 else (crcAdvance (8 * length.toInt.toNat) 0x80000000).toUInt64

/-- Mathematical CRC combination, with zero for a rejected negative length. -/
def crcCombined (first second : UInt64) (length : Int64) : UInt64 :=
  if length.toInt < 0 then 0
  else ((crcAdvance (8 * length.toInt.toNat) first.toUInt32) ^^^ second.toUInt32).toUInt64

/-- `uLong crc32_z(uLong crc, const Bytef *buf, z_size_t len)`.
All readable represented buffers, alignments, seeds and 64-bit lengths. NULL returns zero.
The exact RFC recurrence is returned and the heap is unchanged. -/
def Goal.crc32_z : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt64) (bytes : List UInt8),
    CrcGlobals h → BufferBytes h pointer length.toNat bytes →
    C.run (Zlib.Crc32.crc32_z seed pointer length) h =
      .ok ((if pointer = .null then 0 else (ZlibF.Spec.crc32Update seed.toUInt32 bytes).toUInt64), h)

/-- `uLong crc32(uLong crc, const Bytef *buf, uInt len)`.
The public 32-bit length entry has the same full buffer domain and exact checksum contract. -/
def Goal.crc32 : Prop :=
  ∀ (h : Heap) (seed : UInt64) (pointer : BPtr) (length : UInt32) (bytes : List UInt8),
    CrcGlobals h → BufferBytes h pointer length.toNat bytes →
    C.run (Zlib.Crc32.crc32 seed pointer length) h =
      .ok ((if pointer = .null then 0 else (ZlibF.Spec.crc32Update seed.toUInt32 bytes).toUInt64), h)

/-- `const z_crc_t *get_crc_table(void)`.
The returned table is static and read-only, has 256 entries given by the reflected CRC
recurrence, and leaves every heap observation unchanged. -/
def Goal.get_crc_table : Prop :=
  ∀ h : Heap, CrcGlobals h → ∃ pointer table,
    C.run Zlib.Crc32.get_crc_table h = .ok (pointer, h) ∧
    pointer = .ref .st_crc_table 0 ∧ Space.get h URef.st_crc_table = some table ∧
    Space.ro h URef.st_crc_table = true ∧ table.size = 256 ∧
    ∀ i : Fin 256, table[i.val]? = some (ZlibF.Spec.crcByte 0 (UInt8.ofNat i.val))

/-- Operator generation is total for every signed argument. Initialised globals are preserved;
negative lengths return zero and nonnegative lengths give the mathematical polynomial. -/
def CrcGenerate (program : Int64 → M UInt64) : Prop :=
  ∀ (h : Heap) (length : Int64), CrcGlobals h →
    C.run (program length) h = .ok (crcOperator length, h)

/-- `uLong crc32_combine_gen(z_off_t len2)`; complete operator-generation contract. -/
def Goal.crc32_combine_gen : Prop := CrcGenerate Zlib.Crc32.crc32_combine_gen

/-- `uLong crc32_combine_gen64(z_off64_t len2)`; complete operator-generation contract. -/
def Goal.crc32_combine_gen64 : Prop := CrcGenerate Zlib.Crc32.crc32_combine_gen64

/-- `uLong crc32_combine_op(uLong crc1, uLong crc2, uLong op)`.
`zlib.h` requires an operator generated from a length by `crc32_combine_gen`. The domain here
is exactly those mathematical operators, including its zero rejection result. Arbitrary forged
operators are not promised termination. Every permitted call has the polynomial result and
preserves the whole heap. -/
def Goal.crc32_combine_op : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64), CrcGlobals h →
    C.run (Zlib.Crc32.crc32_combine_op first second (crcOperator length)) h =
      .ok (crcCombined first second length, h)

/-- Total CRC combination, exact polynomial result and the entire heap frame for every signed
length and checksum argument. Negative lengths return zero. -/
def CrcCombine (program : UInt64 → UInt64 → Int64 → M UInt64) : Prop :=
  ∀ (h : Heap) (first second : UInt64) (length : Int64), CrcGlobals h →
    C.run (program first second length) h = .ok (crcCombined first second length, h)

/-- `uLong crc32_combine(uLong crc1, uLong crc2, z_off_t len2)`; full combine contract. -/
def Goal.crc32_combine : Prop := CrcCombine Zlib.Crc32.crc32_combine

/-- `uLong crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)`; full combine contract. -/
def Goal.crc32_combine64 : Prop := CrcCombine Zlib.Crc32.crc32_combine64

end ZlibF.Spec.Public
