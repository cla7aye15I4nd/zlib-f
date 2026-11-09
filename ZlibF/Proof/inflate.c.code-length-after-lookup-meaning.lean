import ZlibF.Proof.«inflate.c.code-length-parser-step»
import ZlibF.Proof.«inflate.c.code-length-zero-repeat»
import ZlibF.Proof.«inflate.c.code-length-previous-repeat»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The real suffix after a decoded ordinary cell implements the matching
independent CodeLens constructor. The pure decoded-symbol observation is
supplied by the actual lookup theorem; it is not a called-program contract.
Normal returns derive repeat validity from the actual checks. -/
theorem clAfterLookup_parser_step {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (small : here.val.toNat < 19)
    (decoded : decodeSym alphabet (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (actual : runX (clAfterLookup c here) l h = .ok ((.ok false, regs), after)) :
    ∃ used state, used ≤ bs.length ∧ after = setI h zs state ∧ BitInv after regs (bs.drop used) ∧
      LengthParserStep alphabet (s.nlen.toNat + s.ndist.toNat) s (stream l bs) state (stream regs (bs.drop used)) := by
  have prefixLength : (actualLengthPrefix s).length = s.«have».toNat :=
    Zlib.Inftrees.Proofs.lensOf_length _ _
  have prefixMore : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  by_cases literal : here.val < 16
  · have literalNat : here.val.toNat < 16 := UInt16.lt_iff_toNat_lt.mp literal
    obtain ⟨run, inv, remaining, _count, _values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) literalNat width enough B initialized
    rw [run] at actual
    cases actual
    refine ⟨0, clWrite s here.val, by omega, rfl, ?_, ?_⟩
    · simpa only [List.drop_zero] using inv
    · intro suffix lengths completion
      have prefixEq := clWrite_lens_prefix (value := here.val) (by omega : s.«have».toNat < 320) (by omega)
      change actualLengthPrefix (clWrite s here.val) = actualLengthPrefix s ++ [here.val.toNat] at prefixEq
      simp only [List.drop_zero] at completion
      rw [prefixEq, remaining] at completion
      exact CodeLens.len prefixMore decoded literalNat completion
  · by_cases previous : here.val = 16
    · rw [clAfterLookup_repeat16 c here previous] at actual
      obtain ⟨used, state, value, bound, heapEq, inv, nonempty, _frame, _size, count, upper, read, prefixEq⟩ :=
        clPreviousRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here width actual
      refine ⟨used, state, bound, heapEq, inv, ?_⟩
      intro suffix lengths completion
      rw [prefixEq] at completion
      have decode16 : decodeSym alphabet (stream l bs) = some (16, (stream l bs).drop here.bits.toNat) := by
        simpa only [previous, show (16 : UInt16).toNat = 16 by decide] using decoded
      have notEmpty : actualLengthPrefix s ≠ [] := by
        intro empty
        have emptyLength := congrArg List.length empty
        simp only [prefixLength, List.length_nil] at emptyLength
        omega
      exact CodeLens.rep16 prefixMore decode16 notEmpty read (by omega) completion
    · by_cases zero17 : here.val = 17
      · rw [clAfterLookup_zero17 c here zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 3 3
            width (by decide) (by decide) (by decide) actual
        simp only [show (3 : UInt32).toNat = 3 by decide] at count read prefixEq
        refine ⟨used, state, bound, heapEq, inv, ?_⟩
        intro suffix lengths completion
        rw [prefixEq] at completion
        have decode17 : decodeSym alphabet (stream l bs) = some (17, (stream l bs).drop here.bits.toNat) := by
          simpa only [zero17, show (17 : UInt16).toNat = 17 by decide] using decoded
        exact CodeLens.rep17 prefixMore decode17 read (by omega) completion
      · have not16 : here.val.toNat ≠ 16 := by
          intro same
          exact previous (UInt16.toNat_inj.mp same)
        have not17 : here.val.toNat ≠ 17 := by
          intro same
          exact zero17 (UInt16.toNat_inj.mp same)
        have notLiteral : ¬ here.val.toNat < 16 := (not_congr UInt16.lt_iff_toNat_lt).mp literal
        have symbol18 : here.val = 18 := UInt16.toNat_inj.mp (by change here.val.toNat = 18; omega)
        rw [clAfterLookup_zero18 c here literal previous zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 7 11
            width (by decide) (by decide) (by decide) actual
        simp only [show (7 : UInt32).toNat = 7 by decide, show (11 : UInt32).toNat = 11 by decide] at count read prefixEq
        refine ⟨used, state, bound, heapEq, inv, ?_⟩
        intro suffix lengths completion
        rw [prefixEq] at completion
        have decode18 : decodeSym alphabet (stream l bs) = some (18, (stream l bs).drop here.bits.toNat) := by
          simpa only [symbol18, show (18 : UInt16).toNat = 18 by decide] using decoded
        exact CodeLens.rep18 prefixMore decode18 read (by omega) completion

#print axioms clAfterLookup_parser_step
end Zlib.Inflate.Proofs
