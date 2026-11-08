import ZlibF.Proof.«inffast.c.dist-bit-ledger»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Counts attached to the same actual cursor are unique. This uses the
pointer offset, not uniqueness of the input byte contents. -/
theorem input_count_eq_of_cursor {ref : BRef} {start a b : Nat} {finish : BPtr}
    (first : finish = inputAdvance (.ref ref start) a)
    (second : finish = inputAdvance (.ref ref start) b) : a = b := by
  have same := first.symm.trans second
  change Ptr.ref ref (start + a) = Ptr.ref ref (start + b) at same
  have offsets := (Ptr.ref.inj same).2
  omega

/-- The actual distance-extra fragment accounts for zero, one or two
input bytes and precisely its selected drop count. The extra-width premise
is an internal safe-table fact; no lower held-bit assumption is needed. -/
theorem dodistBase_two_pull_bit_ledger (c : Ctx) (l : L)
    (width : l.op.toNat ≤ 13) :
    ValuePost (dodistBase c l)
      (fun result => ∃ pulled, pulled ≤ 2 ∧
        result.in_ = inputAdvance l.in_ pulled ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat + 8 * pulled) := by
  intro h result after run
  unfold dodistBase at run
  by_cases first : l.bits < l.op
  · have small := UInt32.lt_iff_toNat_lt.mp first
    simp only [first, ite_true, bind_app] at run
    cases read1 : pull l h with
    | error fault => simp only [read1] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      simp only [read1] at run
      have bits1 := pull_input_bit_budget l (by omega) h one heap1 read1
      have op1 := pull_op_frame l h one heap1 read1
      by_cases second : one.bits < one.op
      · have small1 := UInt32.lt_iff_toNat_lt.mp second
        have opBound : one.op.toNat ≤ 13 := by rw [op1]; exact width
        simp only [second, ite_true, bind_app] at run
        cases read2 : pull one heap1 with
        | error fault => simp only [read2] at run; cases run
        | ok pair =>
          obtain ⟨two, heap2⟩ := pair
          simp only [read2] at run
          have bits2 := pull_input_bit_budget one (by omega) heap1 two heap2 read2
          have op2 := pull_op_frame one heap1 two heap2 read2
          have available : two.op.toNat ≤ two.bits.toNat := by
            rw [op2, op1, bits2.2, bits1.2]
            omega
          have done := distCont_input_bit_ledger c two available heap2 result after run
          refine ⟨2, by omega, ?_, ?_⟩
          · rw [done.1, bits2.1, bits1.1, inputAdvance_add]
          · rw [op2, op1] at done
            omega
      · simp only [second, ite_false] at run
        have available : one.op.toNat ≤ one.bits.toNat := by
          have notLess : ¬ one.bits.toNat < one.op.toNat := by
            intro less
            exact second (UInt32.lt_iff_toNat_lt.mpr less)
          omega
        have done := distCont_input_bit_ledger c one available heap1 result after run
        refine ⟨1, by omega, done.1.trans bits1.1, ?_⟩
        rw [op1] at done
        omega
  · simp only [first, ite_false] at run
    have available : l.op.toNat ≤ l.bits.toNat := by
      have notLess : ¬ l.bits.toNat < l.op.toNat := by
        intro less
        exact first (UInt32.lt_iff_toNat_lt.mpr less)
      omega
    have done := distCont_input_bit_ledger c l available h result after run
    exact ⟨0, by omega, by simpa only [inputAdvance_zero] using done.1,
      by simpa using done.2⟩

#print axioms dodistBase_two_pull_bit_ledger
#print axioms input_count_eq_of_cursor
end Zlib.Inffast.Proofs
