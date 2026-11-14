import ZlibF.Spec.Public.Queries
import ZlibF.Spec.Functional.Queries

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
  · have bound : i < strTable.size := by
      by_cases inside : i < strTable.size
      · exact inside
      · have missing : strTable[i]? = none := Array.getElem?_eq_none (by omega)
        rw [missing] at hi
        cases hi
    change staticStringBytes h i = some (strBytes ZLIB_VERSION)
    rw [staticStringBytes, if_pos bound, hi]
    rfl

#print axioms zlibVersion
end ZlibF.Spec.Public.Proofs
