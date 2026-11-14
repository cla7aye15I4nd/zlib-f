import ZlibF.Spec.Public.Calls

/-!
# Public checksum contracts

The buffer domain includes NULL queries and every represented readable byte object, not
only heap byte blocks. Every result preserves the entire heap. No library callee contract
is assumed. CRC tables are the library's initialised globals, not caller-selected tables.
-/

namespace ZlibF.Spec.Public
open C

/-- The bytes of a readable public buffer. NULL is a documented initial-value query even for
a nonzero length. A nonnull pointer may be one past its object for a zero-length read. -/
def BufferBytes (h : Heap) (pointer : BPtr) (length : Nat) (bytes : List UInt8) : Prop :=
  (pointer = .null ∧ bytes = []) ∨
  ∃ reference offset data, pointer = .ref reference offset ∧
    Space.get h reference = some data ∧ offset + length ≤ data.size ∧
    bytes = (data.toList.drop offset).take length

/-- Adler initialization queries require a NULL pointer and zero length. This is an
explicit restriction relative to the pinned header's unrestricted NULL wording;
see `docs/deviations.md`. Nonnull readable objects retain their full length domain. -/
def AdlerBufferBytes (h : Heap) (pointer : BPtr) (length : Nat) (bytes : List UInt8) : Prop :=
  BufferBytes h pointer length bytes ∧ (pointer = .null → length = 0)

/-- The fixed CRC globals of the selected build. -/
def CrcGlobals (h : Heap) : Prop :=
  h.static.crc_table = Zlib.Crc32H.crc_table ∧
  h.static.x2n_table = Zlib.Crc32H.x2n_table

/-- Canonicalise the low two component sums of an Adler seed. -/
def adlerStart (seed : UInt64) : UInt32 :=
  UInt32.ofNat ((seed.toNat % 65536) % 65521 +
    65536 * ((seed.toNat / 65536 % 65536) % 65521))

end ZlibF.Spec.Public
