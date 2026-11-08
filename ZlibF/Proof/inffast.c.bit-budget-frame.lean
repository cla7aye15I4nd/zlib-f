import ZlibF.Proof.«inffast.c.input-origin-bridge»
import ZlibF.Proof.«inffast.c.base»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual low-bit drop keeps the input cursor and charges exactly
the available bits. Availability is an internal decoder-stage fact; an
arbitrary unsigned subtraction would not give this natural-number budget. -/
theorem drop_input_bit_budget (l : L) (count : UInt32)
    (available : count.toNat ≤ l.bits.toNat) :
    ValuePost (do
      let hold ← shr64 l.hold count.toUInt64
      pure { l with hold, bits := l.bits - count })
      (fun result => result.in_ = l.in_ ∧
        result.bits.toNat + count.toNat = l.bits.toNat) := by
  apply valuePost_bind_any
  intro hold
  apply valuePost_pure
  refine ⟨rfl, ?_⟩
  change (l.bits - count).toNat + count.toNat = l.bits.toNat
  rw [u32_toNat_sub available]
  omega

#print axioms drop_input_bit_budget

theorem pull_op_frame (l : L) : ValuePost (pull l) (fun result => result.op = l.op) := by
  unfold pull
  apply valuePost_bind_any; intro byte
  apply valuePost_bind_any; intro next
  apply valuePost_bind_any; intro shifted
  exact valuePost_pure rfl

/-- With five held bits and at most thirteen extra distance bits, the
actual second conditional pull is unreachable. These are internal table
and refill facts, not extra public input-buffer premises. -/
theorem distance_extra_one_pull_cursor (l : L)
    (held : 5 ≤ l.bits.toNat) (extra : l.op.toNat ≤ 13) :
    ValuePost
      (if l.bits < l.op then do
        let one ← pull l
        if one.bits < one.op then pull one else pure one
       else pure l)
      (fun result => ∃ used, used ≤ 1 ∧
        result.in_ = Zlib.Inflate.Proofs.inputAdvance l.in_ used) := by
  intro h result after run
  by_cases first : l.bits < l.op
  · have lower := UInt32.lt_iff_toNat_lt.mp first
    simp only [first, ite_true, bind_app] at run
    cases pulled : pull l h with
    | error fault => simp only [pulled] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      simp only [pulled] at run
      have bits := pull_input_bit_budget l (by omega) h one heap1 pulled
      have op := pull_op_frame l h one heap1 pulled
      have enough : ¬ one.bits < one.op := by
        intro again
        have small := UInt32.lt_iff_toNat_lt.mp again
        rw [bits.2, op] at small
        omega
      simp only [enough, ite_false, pure_app] at run
      cases run
      exact ⟨1, by omega, bits.1⟩
  · simp only [first, ite_false, pure_app] at run
    cases run
    exact ⟨0, by omega, (Zlib.Inflate.Proofs.inputAdvance_zero l.in_).symm⟩

#print axioms distance_extra_one_pull_cursor
end Zlib.Inffast.Proofs
