import ZlibF.Proof.«crc32.c»

/-!
# CRC correctness on every represented byte-array view

The heap's non-block base residues are universally quantified. The caller
supplies readable bytes, not an alignment restriction or a callee contract.
The independent checksum definition remains unchanged.
-/

namespace Zlib.Crc32.Spec.ByteViews
open C Zlib.Crc32.Proofs

/-- `uLong crc32_z(uLong crc, const unsigned char *buf, z_size_t len)`.
All represented byte arrays and every origin residue are included. This
retains the existing raw theorem's full length and arithmetic domain. -/
def Goal.crc32_z_all_byte_views : Prop :=
  ∀ (h : Heap), StaticsOK h →
    ∀ (crc : UInt64) (ref : BRef) (offset : Nat) (bytes : Array UInt8),
      Space.get h ref = some bytes →
      ∀ len : UInt64, offset + len.toNat ≤ bytes.size →
        C.run (crc32_z crc (.ref ref offset) len) h =
          .ok ((ZlibF.Spec.crc32Update crc.toUInt32
            ((bytes.toList.drop offset).take len.toNat)).toUInt64, h)

/-- `uLong crc32(uLong crc, const unsigned char *buf, uInt len)`.
The compatibility wrapper has the same view and origin coverage. -/
def Goal.crc32_all_byte_views : Prop :=
  ∀ (h : Heap), StaticsOK h →
    ∀ (crc : UInt64) (ref : BRef) (offset : Nat) (bytes : Array UInt8),
      Space.get h ref = some bytes →
      ∀ len : UInt32, offset + len.toNat ≤ bytes.size →
        C.run (crc32 crc (.ref ref offset) len) h =
          .ok ((ZlibF.Spec.crc32Update crc.toUInt32
            ((bytes.toList.drop offset).take len.toNat)).toUInt64, h)

end Zlib.Crc32.Spec.ByteViews
