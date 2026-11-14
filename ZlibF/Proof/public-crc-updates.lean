import ZlibF.Spec.Public.Checksums
import ZlibF.Proof.«crc32.c.views»
import ZlibF.Spec.Functional.Checksums

/-!
# Complete public CRC update results

The public buffer relation includes every represented byte-array view,
zero-length one-past reads, and null initial-value queries of any length.
The actual views theorems retain arbitrary address residues and seeds.
-/

namespace ZlibF.Spec.Public.Proofs
open C

/-- `uLong crc32_z(uLong crc, const Bytef *buf, z_size_t len)`.
Every public readable buffer and null query has its exact CRC result,
without changing any heap field. -/
theorem crc32_z : Goal.crc32_z := by
  intro h seed pointer length bytes globals readable
  rcases readable with ⟨rfl,rfl⟩ | ⟨ref,offset,data,rfl,get,bounds,rfl⟩
  · simpa only [ite_true] using Zlib.Crc32.Proofs.crc32_z_null h seed length
  · simpa only [reduceCtorEq,ite_false] using
      Zlib.Crc32.Proofs.crc32_z_all_byte_views h globals seed ref offset data get length bounds

/-- `uLong crc32(uLong crc, const Bytef *buf, uInt len)`.
The compatibility entry retains the full public buffer domain, every
32-bit length and seed, and the complete immutable-heap result. -/
theorem crc32 : Goal.crc32 := by
  intro h seed pointer length bytes globals readable
  rcases readable with ⟨rfl,rfl⟩ | ⟨ref,offset,data,rfl,get,bounds,rfl⟩
  · simpa only [ite_true] using Zlib.Crc32.Proofs.crc32_null h seed length
  · simpa only [reduceCtorEq,ite_false] using
      Zlib.Crc32.Proofs.crc32_all_byte_views h globals seed ref offset data get length bounds

end ZlibF.Spec.Public.Proofs
