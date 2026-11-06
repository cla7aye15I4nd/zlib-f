import ZlibF.Spec.Api.Examples

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

/-- Every complete gzip member has the header recognized by the gzip reader model. -/
theorem gzip_looks_gzip {stream output : List UInt8} (hd : Gzip.Decodes stream output) :
    GzLooksGzip stream := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, s, hflg, _, _, _, _, hz, _⟩ := hd
  rw [hz, ZlibF.Spec.Proofs.header_eq]
  simp [GzLooksGzip, hflg]

/-- A successfully closed abstract gzip writer yields a file decoded to its input by the
abstract reader. This does not establish refinement of the translated file operations. -/
theorem gz_roundtrip : Goal.gz_roundtrip := by
  intro h rc final hmode hbase hfailed hdirect hclose hrc
  have hw : h.mode ≠ .read := by rw [hmode]; decide
  obtain ⟨m, hm, _, hdecode⟩ := ((hclose.2.2.2 hw hfailed hrc).2 hdirect)
  rw [hbase] at hm
  simp only [List.nil_append] at hm
  rw [hm]
  refine Or.inr (Or.inr ⟨Or.inl (gzip_looks_gzip hdecode), [(m, h.written)], [], ?_, ?_, ?_, ?_⟩)
  · simpa using hdecode
  · simp
  · rintro ⟨m', o, t, he, hd⟩
    have hm' : m' = [] := (List.append_eq_nil_iff.mp he.symm).1
    subst m'
    exact gzip_empty o hd
  · exact Or.inl ⟨rfl, by simp, by simp, rfl⟩

#print axioms gzip_looks_gzip
#print axioms gz_roundtrip
end ZlibF.Spec.Api.Proofs
