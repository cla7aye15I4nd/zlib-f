import ZlibF.Proof.«inffast.c.input-origin-bridge»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Successful byte-cursor advances compose through an actual monadic bind.
The two costs are bounds on successful returns, not callee contracts. -/
theorem cursorPost_bind {first : M L} {next : L → M L}
    (origin : BPtr) (a b : Nat)
    (firstPost : ValuePost first (fun one => ∃ used, used ≤ a ∧
      one.in_ = inputAdvance origin used))
    (nextPost : ∀ one, ValuePost (next one)
      (fun result => ∃ used, used ≤ b ∧
        result.in_ = inputAdvance one.in_ used)) :
    ValuePost (first >>= next) (fun result => ∃ used, used ≤ a + b ∧
      result.in_ = inputAdvance origin used) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨one, heap1⟩ := pair
    rw [firstRun] at run
    obtain ⟨used1, bound1, cursor1⟩ := firstPost h one heap1 firstRun
    obtain ⟨used2, bound2, cursor2⟩ := nextPost one heap1 result after run
    refine ⟨used1 + used2, by omega, ?_⟩
    rw [cursor2, cursor1, inputAdvance_add]

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

/-- The two unconditional pulls under the length-refill condition have
an exact two-byte cursor increment when that branch returns. -/
theorem dolen_refill_cursor (l : L) :
    ValuePost
      (if l.bits < 15 then do
        let one ← pull l
        pull one
       else pure l)
      (fun result => ∃ used, (used = 0 ∨ used = 2) ∧
        result.in_ = inputAdvance l.in_ used) := by
  intro h result after run
  by_cases refill : l.bits < 15
  · simp only [refill, ite_true] at run
    rw [bind_app] at run
    cases pulled : pull l h with
    | error fault => rw [pulled] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      rw [pulled] at run
      have oneCursor := (pull_input_cursor l) h one heap1 pulled
      have twoCursor := (pull_input_cursor one) heap1 result after run
      refine ⟨2, Or.inr rfl, ?_⟩
      rw [twoCursor.1, oneCursor.1, inputAdvance_add]
  · simp only [refill, ite_false, pure_app] at run
    cases run
    exact ⟨0, Or.inl rfl, (inputAdvance_zero l.in_).symm⟩

/-- The optional length-extra pull advances the input by at most one. -/
theorem dolen_extra_cursor (l : L) :
    ValuePost
      (if l.bits < l.op then pull l else pure l)
      (fun result => ∃ used, used ≤ 1 ∧
        result.in_ = inputAdvance l.in_ used) := by
  intro h result after run
  by_cases extra : l.bits < l.op
  · simp only [extra, ite_true] at run
    exact ⟨1, by omega, ((pull_input_cursor l) h result after run).1⟩
  · simp only [extra, ite_false, pure_app] at run
    cases run
    exact ⟨0, by omega, (inputAdvance_zero l.in_).symm⟩

#print axioms dodist_two_pulls_cursor
#print axioms dolen_refill_cursor
#print axioms dolen_extra_cursor
#print axioms cursorPost_bind
end Zlib.Inffast.Proofs
