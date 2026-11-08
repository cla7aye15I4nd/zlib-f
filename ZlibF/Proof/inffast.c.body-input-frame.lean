import ZlibF.Proof.«inffast.c.dolen-loop-input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every successful pass of the actual fast body keeps its input cursor
in the caller byte object. The syntax-only bound is seven pulls; safe
table widths later strengthen the initial-refill branch to six. -/
theorem inflate_fast_body_input_cursor (c : Ctx) (l : L) :
    ValuePost (inflate_fast_body c l)
      (fun result => ∃ used, used ≤ 7 ∧
        result.in_ = inputAdvance l.in_ used) := by
  intro h result after run
  unfold inflate_fast_body at run
  by_cases initial : l.bits < 15
  · simp only [initial, ite_true, bind_app] at run
    cases first : pull l h with
    | error fault => simp only [first] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      simp only [first] at run
      have firstCursor := (pull_input_cursor l) h one heap1 first
      cases second : pull one heap1 with
      | error fault => simp only [second] at run; cases run
      | ok pair =>
        obtain ⟨two, heap2⟩ := pair
        simp only [second] at run
        have secondCursor := (pull_input_cursor one) heap1 two heap2 second
        cases added : c.lcode.add (two.hold &&& c.lmask.toUInt64).toNat heap2 with
        | error fault => simp only [added] at run; cases run
        | ok pair =>
          obtain ⟨here, heap3⟩ := pair
          simp only [added] at run
          obtain ⟨used, bound, cursor⟩ :=
            dolen_loop_input_cursor c { two with here } heap3 result after run
          refine ⟨2 + used, by omega, ?_⟩
          rw [cursor, secondCursor.1, firstCursor.1]
          simp only [inputAdvance_add]
  · simp only [initial, ite_false, bind_app] at run
    cases added : c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat h with
    | error fault => simp only [added] at run; cases run
    | ok pair =>
      obtain ⟨here, heap1⟩ := pair
      simp only [added] at run
      obtain ⟨used, bound, cursor⟩ :=
        dolen_loop_input_cursor c { l with here } heap1 result after run
      exact ⟨used, by omega, by simpa only using cursor⟩

/-- When the fast body skips its initial refill, the actual length loop
can pull at most five bytes. -/
theorem inflate_fast_body_no_initial_pull_cursor (c : Ctx) (l : L)
    (enoughBits : ¬ l.bits < 15) :
    ValuePost (inflate_fast_body c l)
      (fun result => ∃ used, used ≤ 5 ∧
        result.in_ = inputAdvance l.in_ used) := by
  intro h result after run
  unfold inflate_fast_body at run
  simp only [enoughBits, ite_false, bind_app] at run
  cases added : c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat h with
  | error fault => simp only [added] at run; cases run
  | ok pair =>
    obtain ⟨here, heap1⟩ := pair
    simp only [added] at run
    obtain ⟨used, bound, cursor⟩ :=
      dolen_loop_input_cursor c { l with here } heap1 result after run
    exact ⟨used, bound, by simpa only using cursor⟩

#print axioms inflate_fast_body_input_cursor
#print axioms inflate_fast_body_no_initial_pull_cursor
end Zlib.Inffast.Proofs
