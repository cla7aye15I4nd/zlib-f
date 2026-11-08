import ZlibF.Proof.«inffast.c.dolen-input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual length-table loop reads at most five bytes in total.
Continuation iterations only move the table cursor and do not pull. -/
theorem dolen_loop_input_cursor (c : Ctx) (l : L) :
    ValuePost (cdoWhile (dolen c) (fun q => pure (q.againL, q)) l)
      (fun result => ∃ used, used ≤ 5 ∧
        result.in_ = inputAdvance l.in_ used) := by
  have key : ∀ n start,
      ValuePost (cdoWhile.go (dolen c) (fun q => pure (q.againL, q)) n start)
        (fun result => ∃ used, used ≤ 5 ∧
          result.in_ = inputAdvance start.in_ used) := by
    intro n
    induction n with
    | zero => intro start h result after run; cases run
    | succ n ih =>
      intro start h result after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : dolen c start h with
      | error fault => simp only [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        simp only [executed, pure_app] at run
        cases flag : middle.againL with
        | false =>
          simp only [flag, Bool.false_eq_true, ite_false, pure_app] at run
          cases run
          exact dolen_input_cursor c start h result after executed
        | true =>
          simp only [flag, ite_true] at run
          obtain ⟨used, bound, cursor⟩ := ih middle heap1 result after run
          have unchanged := dolen_continue_cursor c start h middle heap1 executed flag
          rw [unchanged] at cursor
          exact ⟨used, bound, cursor⟩
  exact key fuel l

#print axioms dolen_loop_input_cursor
end Zlib.Inffast.Proofs
