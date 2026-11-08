import ZlibF.Proof.«inffast.c.input-origin-bridge»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The exact two conditional pulls in the distance-base path advance the
input cursor by zero, one or two bytes on every successful return. -/
theorem dodist_two_pulls_cursor (l : L) :
    ValuePost
      (if l.bits < l.op then do
        let one ← pull l
        if one.bits < one.op then pull one else pure one
       else pure l)
      (fun result => ∃ used, used ≤ 2 ∧
        result.in_ = inputAdvance l.in_ used) := by
  intro h result after run
  by_cases first : l.bits < l.op
  · simp only [first, ite_true] at run
    rw [bind_app] at run
    cases pulled : pull l h with
    | error fault => rw [pulled] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      rw [pulled] at run
      have oneCursor := (pull_input_cursor l) h one heap1 pulled
      by_cases second : one.bits < one.op
      · simp only [second, ite_true] at run
        have twoCursor := (pull_input_cursor one) heap1 result after run
        refine ⟨2, by omega, ?_⟩
        rw [twoCursor.1, oneCursor.1, inputAdvance_add]
      · simp only [second, ite_false, pure_app] at run
        cases run
        exact ⟨1, by omega, oneCursor.1⟩
  · simp only [first, ite_false, pure_app] at run
    cases run
    exact ⟨0, by omega, (inputAdvance_zero l.in_).symm⟩

#print axioms dodist_two_pulls_cursor
end Zlib.Inffast.Proofs
