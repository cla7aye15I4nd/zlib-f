import ZlibF.Spec.Api.Goals

namespace ZlibF.Spec.Api.Proofs

/-- The `Compress2` model refuses `Z_BUF_ERROR` when the destination has at least
`compressBound` bytes, and its output stays within that bound. This is a property
of the model relation; applying it to translated calls also needs refinement. -/
theorem compress_bound_adequate : Goal.compress_bound_adequate := by
  intro level src cap rc dst hcap hrun
  cases hp : compressParams level with
  | none =>
    simp only [Compress2, Bool.true_eq_false, ↓reduceIte, hp] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨by decide, by simp⟩
  | some p =>
    simp only [Compress2, Bool.true_eq_false, ↓reduceIte, hp] at hrun
    rcases hrun with ⟨rfl, rfl⟩ | ⟨rfl, _, _, hb⟩ | ⟨_, _, hlt, _⟩
    · exact ⟨by decide, by simp⟩
    · exact ⟨by decide, hb⟩
    · omega

end ZlibF.Spec.Api.Proofs
