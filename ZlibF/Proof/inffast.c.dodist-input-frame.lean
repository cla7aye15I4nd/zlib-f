import ZlibF.Proof.«inffast.c.pull-prefix-bridge»

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
end Zlib.Inffast.Proofs
