import ZlibF.Proof.«inflate.c.code-length-after-lookup-meaning»
import ZlibF.Math.«code-length-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A normal actual length iteration consumes a concrete bit prefix whose
independent meaning holds for every future input suffix. Unlike a relation
on one fixed physical chunk, this causal trace can survive buffer replacement. -/
theorem clAfterLookup_prefix_trace {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (small : here.val.toNat < 19)
    (acceptable : Acceptable .codeLength alphabet)
    (decoded : decodeSym alphabet (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (actual : runX (clAfterLookup c here) l h = .ok ((.ok false, regs), after)) :
    ∃ used state consumed, used ≤ bs.length ∧ after = setI h zs state ∧ BitInv after regs (bs.drop used) ∧
      stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
        (actualLengthPrefix s) consumed (actualLengthPrefix state) := by
  have prefixLength : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have prefixMore : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  by_cases literal : here.val < 16
  · have literalNat : here.val.toNat < 16 := UInt16.lt_iff_toNat_lt.mp literal
    obtain ⟨run, inv, remaining, _count, _values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) literalNat width enough B initialized
    rw [run] at actual
    cases actual
    refine ⟨0, clWrite s here.val, codeOf alphabet here.val.toNat, by omega, rfl, ?_, ?_, ?_⟩
    · simpa only [List.drop_zero] using inv
    · simp only [List.drop_zero]
      rw [remaining]
      exact ZlibF.Math.CodeLengthPrefix.decoded_word decoded
    · have prefixEq := clWrite_lens_prefix (value := here.val) (by omega : s.«have».toNat < 320) (by omega)
      change actualLengthPrefix (clWrite s here.val) = actualLengthPrefix s ++ [here.val.toNat] at prefixEq
      rw [prefixEq]
      exact ZlibF.Math.CodeLengthPrefix.Trace.literal acceptable prefixMore
        (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1 literalNat
  · by_cases previous : here.val = 16
    · rw [clAfterLookup_repeat16 c here previous] at actual
      obtain ⟨used, state, value, bound, heapEq, inv, nonempty, _frame, _size, count, upper, read, prefixEq⟩ :=
        clPreviousRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here width actual
      have decode16 : decodeSym alphabet (stream l bs) = some (16, (stream l bs).drop here.bits.toNat) := by
        simpa only [previous, show (16 : UInt16).toNat = 16 by decide] using decoded
      have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode16
      obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
      refine ⟨used, state, codeOf alphabet 16 ++ bitsOfNat value 2, bound, heapEq, inv, ?_, ?_⟩
      · rw [word, extraWord, List.append_assoc]
      · rw [prefixEq]
        have notEmpty : actualLengthPrefix s ≠ [] := by
          intro empty
          have emptyLength := congrArg List.length empty
          simp only [prefixLength, List.length_nil] at emptyLength
          omega
        exact ZlibF.Math.CodeLengthPrefix.Trace.previous acceptable prefixMore
          (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode16).2.1 notEmpty valueBound (by omega)
    · by_cases zero17 : here.val = 17
      · rw [clAfterLookup_zero17 c here zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 3 3
            width (by decide) (by decide) (by decide) actual
        simp only [show (3 : UInt32).toNat = 3 by decide] at count read prefixEq
        have decode17 : decodeSym alphabet (stream l bs) = some (17, (stream l bs).drop here.bits.toNat) := by
          simpa only [zero17, show (17 : UInt16).toNat = 17 by decide] using decoded
        have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode17
        obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
        refine ⟨used, state, codeOf alphabet 17 ++ bitsOfNat value 3, bound, heapEq, inv, ?_, ?_⟩
        · rw [word, extraWord, List.append_assoc]
        · rw [prefixEq]
          exact ZlibF.Math.CodeLengthPrefix.Trace.zero_short acceptable prefixMore
            (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode17).2.1 valueBound (by omega)
      · have not16 : here.val.toNat ≠ 16 := fun same => previous (UInt16.toNat_inj.mp same)
        have not17 : here.val.toNat ≠ 17 := fun same => zero17 (UInt16.toNat_inj.mp same)
        have notLiteral : ¬ here.val.toNat < 16 := (not_congr UInt16.lt_iff_toNat_lt).mp literal
        have symbol18 : here.val = 18 := UInt16.toNat_inj.mp (by change here.val.toNat = 18; omega)
        rw [clAfterLookup_zero18 c here literal previous zero17] at actual
        obtain ⟨used, state, value, bound, heapEq, inv, _frame, _size, count, upper, read, prefixEq⟩ :=
          clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here 7 11
            width (by decide) (by decide) (by decide) actual
        simp only [show (7 : UInt32).toNat = 7 by decide, show (11 : UInt32).toNat = 11 by decide] at count read prefixEq
        have decode18 : decodeSym alphabet (stream l bs) = some (18, (stream l bs).drop here.bits.toNat) := by
          simpa only [symbol18, show (18 : UInt16).toNat = 18 by decide] using decoded
        have word := ZlibF.Math.CodeLengthPrefix.decoded_word decode18
        obtain ⟨valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
        refine ⟨used, state, codeOf alphabet 18 ++ bitsOfNat value 7, bound, heapEq, inv, ?_, ?_⟩
        · rw [word, extraWord, List.append_assoc]
        · rw [prefixEq]
          exact ZlibF.Math.CodeLengthPrefix.Trace.zero_long acceptable prefixMore
            (Zlib.Inftrees.Proofs.decoded_symbol_prefix decode18).2.1 valueBound (by omega)

#print axioms clAfterLookup_prefix_trace
end Zlib.Inflate.Proofs
