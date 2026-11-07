import ZlibF.Spec.Public.Queries

namespace ZlibF.Spec.Public.Proofs
open C

set_option maxRecDepth 100000 in
/-- `const char *zlibVersion(void)`: return the read-only pinned version string. -/
theorem zlibVersion : Goal.zlibVersion := by
  intro h
  have hm : ZLIB_VERSION ∈ strTable := by
    rw [Array.mem_def]
    decide +kernel
  obtain ⟨i, hr, hi⟩ := strLitRef_of_mem (h := h) hm
  refine ⟨.ref (.str i) 0, ?_, i, rfl, ?_, rfl⟩
  · exact hr
  · simp [hi, strBytes]

#print axioms zlibVersion
end ZlibF.Spec.Public.Proofs
