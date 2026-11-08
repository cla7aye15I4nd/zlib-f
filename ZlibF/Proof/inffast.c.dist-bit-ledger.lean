import ZlibF.Proof.«inffast.c.bit-budget-frame»
import ZlibF.Proof.«inffast.c.dodist-input-frame»
import ZlibF.Proof.«inffast.c.dist»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual distance suffix spends precisely the selected extra-bit count.
This is a successful-run observation; safety comes from its caller proof. -/
theorem distCont_input_bit_ledger (c : Ctx) (l : L)
    (available : l.op.toNat ≤ l.bits.toNat) :
    ValuePost (distCont c l)
      (fun result => result.in_ = l.in_ ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat) := by
  intro h result after run
  unfold distCont at run
  simp only [bind_app] at run
  cases shifted : shl32 1 l.op h with
  | error fault => simp only [shifted] at run; cases run
  | ok pair =>
    obtain ⟨mask, heap1⟩ := pair
    simp only [shifted] at run
    cases dropped : shr64 l.hold l.op.toUInt64 heap1 with
    | error fault => simp only [dropped] at run; cases run
    | ok pair =>
      obtain ⟨hold, heap2⟩ := pair
      simp only [dropped] at run
      cases diffed : Ptr.diff l.out c.beg heap2 with
      | error fault => simp only [diffed] at run; cases run
      | ok pair =>
        obtain ⟨distance, heap3⟩ := pair
        simp only [diffed] at run
        let current : L := { l with
          dist := l.dist + (l.hold.toUInt32 &&& mask - 1),
          hold, bits := l.bits - l.op,
          op := distance.toUInt64.toUInt32 }
        have frame := copyMatch_input_registers c current
          heap3 result after (by simpa only [current] using run)
        have cursor : result.in_ = current.in_ := by
          exact congrArg Prod.fst frame
        have bits : result.bits = current.bits := by
          exact congrArg (fun pair => pair.2.1) frame
        refine ⟨cursor, ?_⟩
        rw [bits]
        change (l.bits - l.op).toNat + l.op.toNat = l.bits.toNat
        rw [u32_toNat_sub available]
        omega

/-- With the safe distance extra width, the actual distance base fragment
charges exactly one byte for its optional pull and exactly `op` consumed bits. -/
theorem dodistBase_one_pull_bit_ledger (c : Ctx) (l : L)
    (held : 5 ≤ l.bits.toNat) (width : l.op.toNat ≤ 13) :
    ValuePost (dodistBase c l)
      (fun result => ∃ pulled, pulled ≤ 1 ∧
        result.in_ = Zlib.Inflate.Proofs.inputAdvance l.in_ pulled ∧
        result.bits.toNat + l.op.toNat = l.bits.toNat + 8 * pulled) := by
  intro h result after run
  unfold dodistBase at run
  by_cases need : l.bits < l.op
  · have small : l.bits.toNat ≤ 12 := by
      have less := UInt32.lt_iff_toNat_lt.mp need
      omega
    simp only [need, ite_true, bind_app] at run
    cases first : pull l h with
    | error fault => simp only [first] at run; cases run
    | ok pair =>
      obtain ⟨one, heap1⟩ := pair
      simp only [first] at run
      have pulled := pull_input_bit_budget l (by omega) h one heap1 first
      have opSame := pull_op_frame l h one heap1 first
      have enough : ¬ one.bits < one.op := by
        intro again
        have less := UInt32.lt_iff_toNat_lt.mp again
        rw [pulled.2, opSame] at less
        omega
      simp only [enough, ite_false] at run
      have done := distCont_input_bit_ledger c one (by rw [opSame, pulled.2]; omega)
        heap1 result after run
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [done.1, pulled.1]
      · rw [opSame] at done
        omega
  · simp only [need, ite_false] at run
    have avail : l.op.toNat ≤ l.bits.toNat := by
      have notLess : ¬ l.bits.toNat < l.op.toNat := by
        intro less
        exact need (UInt32.lt_iff_toNat_lt.mpr less)
      omega
    have done := distCont_input_bit_ledger c l avail h result after run
    exact ⟨0, by omega,
      by simpa only [Zlib.Inflate.Proofs.inputAdvance_zero] using done.1,
      by simpa using done.2⟩

#print axioms distCont_input_bit_ledger
#print axioms dodistBase_one_pull_bit_ledger
end Zlib.Inffast.Proofs
