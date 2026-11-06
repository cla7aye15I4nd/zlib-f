import ZlibF.Spec.Api.Examples

namespace ZlibF.Spec.Api.Proofs

private def switched : GzHandle := { gzR with mode := .write }

/-- The seek relation permits the returned handle's mode to change. -/
theorem seek_model_allows_mode_change : GzSeek gzR 0 0 0 switched := by
  simp [GzSeek, GzHandle.tell, GzHandle.CopyMode, gzR, switched, Z.ok, Z.bufError]

/-- The changed handle is then treated as a writer by the read relation. -/
theorem read_model_after_mode_change : GzReadFn switched 1 [] (-1) switched := by
  simp [GzReadFn, switched, gzR]

/-- The existing seek/read goal is false for its current model relations. -/
theorem gz_seek_read_false : ¬ Goal.gz_seek_read := by
  intro goal
  have h := goal gzR switched switched 0 0 0 1 [] (-1)
    rfl rfl (by decide) (Or.inl rfl) seek_model_allows_mode_change (by decide)
  have he := h.2 rfl read_model_after_mode_change
  simp [gzR] at he

#print axioms gz_seek_read_false
end ZlibF.Spec.Api.Proofs
