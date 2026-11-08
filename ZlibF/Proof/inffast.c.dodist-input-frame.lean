import ZlibF.Proof.«inffast.c.pull-prefix-bridge»
import ZlibF.Proof.«inffast.c.copy-control-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

theorem valuePost_weaken {α : Type} {program : M α} {oldPost post : α → Prop}
    (proved : ValuePost program oldPost) (use : ∀ value, oldPost value → post value) :
    ValuePost program post := by
  intro h result after run
  exact use result (proved h result after run)

theorem copyMatch_cursor_bound (c : Ctx) (current : L) (origin : BPtr) (bound : Nat)
    (known : ∃ used, used ≤ bound ∧ current.in_ = inputAdvance origin used) :
    ValuePost (copyMatch c current) (fun result => ∃ used, used ≤ bound ∧
      result.in_ = inputAdvance origin used) := by
  obtain ⟨used, limit, cursor⟩ := known
  intro h result after run
  have frame := copyMatch_input_registers c current h result after run
  have same : result.in_ = current.in_ := congrArg Prod.fst frame
  exact ⟨used, limit, same.trans cursor⟩

set_option maxHeartbeats 1000000 in
/-- The actual distance iteration reads at most two input bytes on a
successful return. This also includes invalid-code and bad-distance exits;
it does not assert safety or termination for arbitrary local registers. -/
theorem dodist_input_cursor (c : Ctx) (l : L) :
    ValuePost (dodist c l) (fun result => ∃ used, used ≤ 2 ∧
      result.in_ = inputAdvance l.in_ used) := by
  unfold dodist
  repeat' first
    | dsimp only
    | (apply valuePost_pure (α := L) (post := fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance l.in_ used)
       first
       | solve | refine ⟨0, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨1, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨2, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add])
    | (apply copyMatch_cursor_bound (origin := l.in_) (bound := 2)
       first
       | solve | refine ⟨0, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨1, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨2, by omega, ?_⟩; simp_all [inputRegisters, inputAdvance_zero, inputAdvance_add])
    | apply valuePost_ite (α := L) (post := fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance l.in_ used)
    | apply valuePost_bind (α := L) (β := L) (post := fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance l.in_ used) (pull_input_cursor _); intro next cursor
    | apply valuePost_bind_any (β := L) (post := fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance l.in_ used); intro next

#print axioms dodist_input_cursor

theorem copyMatch_stopped_cursor (c : Ctx) (current : L) (origin : BPtr)
    (stopped : current.againD = false) :
    ValuePost (copyMatch c current)
      (fun result => result.againD = true → result.in_ = origin) := by
  intro h result after run
  have frame := copyMatch_decode_controls c current h result after run
  have same : result.againD = current.againD := congrArg Prod.fst frame
  simp [same, stopped]

set_option maxHeartbeats 1000000 in
/-- Every actual distance-table continuation retains its input cursor.
Only the terminal base-distance path performs input pulls. -/
theorem dodist_continue_cursor (c : Ctx) (l : L) :
    ValuePost (dodist c l)
      (fun result => result.againD = true → result.in_ = l.in_) := by
  unfold dodist
  repeat' first
    | dsimp only
    | apply valuePost_pure (α := L) (post := fun result => result.againD = true → result.in_ = l.in_); simp_all [decodeControls]
    | apply copyMatch_stopped_cursor (origin := l.in_); simp_all [decodeControls]
    | apply valuePost_ite (α := L) (post := fun result => result.againD = true → result.in_ = l.in_)
    | apply valuePost_bind (α := L) (β := L) (post := fun result => result.againD = true → result.in_ = l.in_) (pull_decode_controls _); intro next controls
    | apply valuePost_bind_any (β := L) (post := fun result => result.againD = true → result.in_ = l.in_); intro next

#print axioms dodist_continue_cursor

/-- The actual distance lookup loop reads at most two bytes in total.
Continuation iterations only relocate the table pointer and read no input. -/
theorem dodist_loop_input_cursor (c : Ctx) (l : L) :
    ValuePost (cdoWhile (dodist c) (fun q => pure (q.againD, q)) l)
      (fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance l.in_ used) := by
  have key : ∀ n start,
      ValuePost (cdoWhile.go (dodist c) (fun q => pure (q.againD, q)) n start)
        (fun result => ∃ used, used ≤ 2 ∧ result.in_ = inputAdvance start.in_ used) := by
    intro n
    induction n with
    | zero => intro start h result after run; cases run
    | succ n ih =>
      intro start h result after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : dodist c start h with
      | error fault => simp only [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        simp only [executed, pure_app] at run
        cases flag : middle.againD with
        | false =>
          simp only [flag, Bool.false_eq_true, ite_false, pure_app] at run
          cases run
          exact dodist_input_cursor c start h result after executed
        | true =>
          simp only [flag, ite_true] at run
          obtain ⟨used, bound, cursor⟩ := ih middle heap1 result after run
          have unchanged := dodist_continue_cursor c start h middle heap1 executed flag
          rw [unchanged] at cursor
          exact ⟨used, bound, cursor⟩
  exact key fuel l

#print axioms dodist_loop_input_cursor

theorem copyMatch_againL_frame (c : Ctx) (current : L) (expected : Bool)
    (initial : current.againL = expected) :
    ValuePost (copyMatch c current) (fun result => result.againL = expected) := by
  intro h result after run
  have frame := copyMatch_decode_controls c current h result after run
  exact (congrArg Prod.snd frame).trans initial

set_option maxHeartbeats 1000000 in
theorem dodist_againL_frame (c : Ctx) (l : L) :
    ValuePost (dodist c l) (fun result => result.againL = l.againL) := by
  unfold dodist
  repeat' first
    | dsimp only
    | apply valuePost_pure (α := L) (post := fun result => result.againL = l.againL); simp_all [decodeControls]
    | apply copyMatch_againL_frame (expected := l.againL); simp_all [decodeControls]
    | apply valuePost_ite (α := L) (post := fun result => result.againL = l.againL)
    | apply valuePost_bind (α := L) (β := L) (post := fun result => result.againL = l.againL) (pull_decode_controls _); intro next controls
    | apply valuePost_bind_any (β := L) (post := fun result => result.againL = l.againL); intro next

theorem dodist_loop_againL_frame (c : Ctx) (l : L) :
    ValuePost (cdoWhile (dodist c) (fun q => pure (q.againD, q)) l)
      (fun result => result.againL = l.againL) :=
  cdoWhile_preserves_view (fun q : L => q.againL) (dodist c)
    (fun q => pure (q.againD, q)) (dodist_againL_frame c)
    (fun _ => valuePost_pure rfl) l

#print axioms dodist_loop_againL_frame
end Zlib.Inffast.Proofs
