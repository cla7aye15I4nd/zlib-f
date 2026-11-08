import ZlibF.Proof.«inffast.c.pull-prefix-bridge»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The translated length-base suffix through distance-root selection reads
at most three bytes: one optional length-extra byte and one two-byte refill.
This is the exact control fragment between setting `len` and looking up
`dcode`; all intervening arithmetic preserves the input cursor. -/
theorem dolen_length_prefix_cursor (l : L) :
    ValuePost (do
      let mut q := l
      if q.op != 0 then
        if q.bits < q.op then q ← pull q
        let m ← shl32 1 q.op
        q := { q with len := q.len + (q.hold.toUInt32 &&& (m - 1)) }
        q := { q with hold := ← shr64 q.hold q.op.toUInt64 }
        q := { q with bits := q.bits - q.op }
      if q.bits < 15 then
        q ← pull q
        q ← pull q
      pure q)
      (fun result => ∃ used, used ≤ 3 ∧
        result.in_ = inputAdvance l.in_ used) := by
  repeat' first
    | dsimp only
    | (apply valuePost_pure (α := L)
        (post := fun result => ∃ used, used ≤ 3 ∧
          result.in_ = inputAdvance l.in_ used)
       first
       | solve | refine ⟨0, by omega, ?_⟩; simp_all [inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨1, by omega, ?_⟩; simp_all [inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨2, by omega, ?_⟩; simp_all [inputAdvance_zero, inputAdvance_add]
       | solve | refine ⟨3, by omega, ?_⟩; simp_all [inputAdvance_zero, inputAdvance_add])
    | apply valuePost_ite (α := L)
        (post := fun result => ∃ used, used ≤ 3 ∧
          result.in_ = inputAdvance l.in_ used)
    | apply valuePost_bind (α := L) (β := L)
        (post := fun result => ∃ used, used ≤ 3 ∧
          result.in_ = inputAdvance l.in_ used)
        (pull_input_cursor _); intro next cursor
    | apply valuePost_bind_any (β := L)
        (post := fun result => ∃ used, used ≤ 3 ∧
          result.in_ = inputAdvance l.in_ used); intro next

#print axioms dolen_length_prefix_cursor
end Zlib.Inffast.Proofs
