import ZlibF.Spec.Public.Checksums

namespace ZlibF.Spec.Public.Proofs
open C

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem crc_table_values : ∀ i : Fin 256,
    Zlib.Crc32H.crc_table[i.val]? = some (ZlibF.Spec.crcByte 0 (UInt8.ofNat i.val)) := by
  decide +kernel

/-- `const z_crc_t *get_crc_table(void)` returns the read-only reflected CRC table. -/
theorem get_crc_table : Goal.get_crc_table := by
  intro h globals
  refine ⟨.ref .st_crc_table 0, Zlib.Crc32H.crc_table, rfl, rfl, ?_, rfl, ?_, crc_table_values⟩
  · simpa using globals.1
  · decide +kernel

#print axioms get_crc_table
end ZlibF.Spec.Public.Proofs
