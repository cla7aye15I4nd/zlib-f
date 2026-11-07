import ZlibF.Spec.Public.Queries

namespace ZlibF.Spec.Public.Proofs
open C Zlib.Zutil

private theorem zError_eval (err : Int32) :
    zError err = strLit (errorText err.toInt) := by
  funext h
  by_cases hr : err < -6 || err > 2
  · have h1 : err.toInt < -6 ∨ 2 < err.toInt := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with hr | hr
      · left; have := Int32.lt_iff_toInt_lt.mp hr; simpa using this
      · right; have := Int32.lt_iff_toInt_lt.mp hr; simpa using this
    have : errorText err.toInt = "" := by
      unfold errorText
      split <;> first | omega | rfl
    rw [this]
    simp [zError, hr, z_errmsg, strLit]
  · have h1 : -6 ≤ err.toInt ∧ err.toInt ≤ 2 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int32.not_lt] at hr
      have a := Int32.le_iff_toInt_le.mp hr.1
      have b := Int32.le_iff_toInt_le.mp hr.2
      simpa using And.intro a b
    obtain ⟨k, hk1, hk2, rfl⟩ : ∃ k : Int, -6 ≤ k ∧ k ≤ 2 ∧ err = Int32.ofInt k :=
      ⟨err.toInt, h1.1, h1.2, (Int32.ofInt_toInt err).symm⟩
    rcases (by omega : k = -6 ∨ k = -5 ∨ k = -4 ∨ k = -3 ∨ k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
private theorem errorText_lit (k : Int) : errorText k ∈ strTable := by
  unfold errorText
  rw [Array.mem_def]
  split <;> decide +kernel

/-- `const char *zError(int err)` returns the public read-only message on every heap. -/
theorem zError : Goal.zError := by
  intro h err
  obtain ⟨i, hr, hi⟩ := strLitRef_of_mem (h := h) (errorText_lit err.toInt)
  refine ⟨.ref (.str i) 0, ?_, i, rfl, ?_, rfl⟩
  · simpa only [C.run, zError_eval, strLit] using hr
  · simp [hi, strBytes]

#print axioms zError
end ZlibF.Spec.Public.Proofs
