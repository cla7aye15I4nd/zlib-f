import ZlibF.Proof.«inflate.c.header-codelens-future-step»
namespace Zlib.Inflate.Proofs.CodeLensFuture
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CodeLensCompletion
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem lookup_suffix_wait {c : Ctx} {h : Heap} {l looked regs : IL}
    (lookupRun : runX (lookup1 c false) l h = .ok ((.ok (), looked), h))
    (suffixRun : runX (clAfterLookup c looked.here) looked h = .ok ((.error Ex.leave, regs), h)) :
    runX (clReadBody c) l h = .ok ((.error Ex.leave, regs), h) := by
  rw [clReadBody_eq, runX_bind, lookupRun]
  simpa only [runX_bind, runX_get] using suffixRun

/-- A valid independent continuation over current+future bits forces one
actual CODELENS iteration either to wait or to write its exact next valid
prefix. Invalid repeat checks cannot be selected on this syntax. -/
theorem body_future
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet out : List Nat} {future rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs ++ future) rest out) :
    (∃ regs, runX (clReadBody c) l h = .ok ((.error Ex.leave, regs), h)) ∨
    (∃ regs state used,
      runX (clReadBody c) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧ ClWriteResult s state ∧
      CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) (stream regs (bs.drop used) ++ future) rest out) := by
  obtain ⟨pointer, _table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  have get := CodeRef.get_istate_codes hs
  have prefixLength : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have witness : (∃ regs, runX (clReadBody c) l h = .ok ((.error Ex.leave, regs), h)) ∨
      (∃ regs state used, runX (clReadBody c) l h = .ok ((.ok false, regs), setI h zs state) ∧
        used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) (stream regs (bs.drop used) ++ future) rest out) := by
    cases parsed with
    | done full => omega
    | len _ decoded literal tail =>
      rcases lookup_future hc hs pointer contents B decoded with ⟨regs, wait⟩ | ⟨looked, used1, lookupRun, bound1, inv1, source1, ordinary, value, seven, fitted, remaining⟩
      · exact Or.inl ⟨regs, by rw [clReadBody_eq, runX_bind, wait]⟩
      · obtain ⟨used, _one, bound, run, inv, _source, actualDecode, written⟩ :=
          clReadBody_literal_symbol hc hs pointer get contents.toCodeLengthMeaning size (by omega) initialized B lookupRun ordinary (by omega)
        have extended := ZlibF.Spec.Proofs.ext_acceptable contents.acceptable _ _ _ future actualDecode
        rw [value] at extended
        have restEq := congrArg Prod.snd (Option.some.inj (extended.symm.trans decoded))
        dsimp only at restEq
        change actualLengthPrefix (clWrite s looked.here.val) = actualLengthPrefix s ++ [looked.here.val.toNat] at written
        refine Or.inr ⟨_, clWrite s looked.here.val, used, run, bound, inv, ?_⟩
        rw [written, value, restEq]
        exact tail
    | rep16 _ decoded nonempty readExtra room tail =>
      rcases lookup_future hc hs pointer contents B decoded with ⟨regs, wait⟩ | ⟨looked, used1, lookupRun, bound1, inv1, source1, _ordinary, value, seven, fitted, remaining⟩
      · exact Or.inl ⟨regs, by rw [clReadBody_eq, runX_bind, wait]⟩
      · have symbol : looked.here.val = 16 := UInt16.toNat_inj.mp value
        have nonemptyCount : 1 ≤ s.«have».toNat := by
          by_cases positive : 1 ≤ s.«have».toNat
          · exact positive
          · have empty : actualLengthPrefix s = [] := List.eq_nil_of_length_eq_zero (by omega)
            exact False.elim (nonempty empty)
        rw [remaining] at readExtra
        rcases previous_repeat_future hr hc hz hs size nlen ndist haveBound nonemptyCount inv1 looked.here seven fitted readExtra (by omega) with ⟨regs, wait⟩ | ⟨regs, state, used2, currentRest, run, bound2, inv2, source2, written, remaining2⟩
        · rw [← clAfterLookup_repeat16 c looked.here symbol] at wait
          exact Or.inl ⟨regs, lookup_suffix_wait lookupRun wait⟩
        · rw [← clAfterLookup_repeat16 c looked.here symbol] at run
          obtain ⟨actual, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 run bound2 inv2
          refine Or.inr ⟨regs, state, used1 + used2, actual, bound, inv, ?_⟩
          rw [written]
          rw [List.drop_drop] at source2
          rw [source2, remaining2]
          exact tail
    | rep17 _ decoded readExtra room tail =>
      rcases lookup_future hc hs pointer contents B decoded with ⟨regs, wait⟩ | ⟨looked, used1, lookupRun, bound1, inv1, source1, _ordinary, value, seven, fitted, remaining⟩
      · exact Or.inl ⟨regs, by rw [clReadBody_eq, runX_bind, wait]⟩
      · have symbol : looked.here.val = 17 := UInt16.toNat_inj.mp value
        rw [remaining] at readExtra
        rcases zero_repeat_future hc hs size nlen ndist haveBound inv1 looked.here 3 3 seven (by decide) (by decide) (by decide) fitted readExtra (by simpa only [prefixLength, show (3 : UInt32).toNat = 3 by decide] using room) with ⟨regs, wait⟩ | ⟨regs, state, used2, currentRest, run, bound2, inv2, source2, written, remaining2⟩
        · rw [← clAfterLookup_zero17 c looked.here symbol] at wait
          exact Or.inl ⟨regs, lookup_suffix_wait lookupRun wait⟩
        · rw [← clAfterLookup_zero17 c looked.here symbol] at run
          obtain ⟨actual, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 run bound2 inv2
          refine Or.inr ⟨regs, state, used1 + used2, actual, bound, inv, ?_⟩
          rw [written]
          rw [List.drop_drop] at source2
          rw [source2, remaining2]
          exact tail
    | rep18 _ decoded readExtra room tail =>
      rcases lookup_future hc hs pointer contents B decoded with ⟨regs, wait⟩ | ⟨looked, used1, lookupRun, bound1, inv1, source1, _ordinary, value, seven, fitted, remaining⟩
      · exact Or.inl ⟨regs, by rw [clReadBody_eq, runX_bind, wait]⟩
      · have symbol : looked.here.val = 18 := UInt16.toNat_inj.mp value
        have notLiteral : ¬ looked.here.val < 16 := by rw [symbol]; decide
        have not16 : looked.here.val ≠ 16 := by rw [symbol]; decide
        have not17 : looked.here.val ≠ 17 := by rw [symbol]; decide
        rw [remaining] at readExtra
        rcases zero_repeat_future hc hs size nlen ndist haveBound inv1 looked.here 7 11 seven (by decide) (by decide) (by decide) fitted readExtra (by simpa only [prefixLength, show (11 : UInt32).toNat = 11 by decide] using room) with ⟨regs, wait⟩ | ⟨regs, state, used2, currentRest, run, bound2, inv2, source2, written, remaining2⟩
        · rw [← clAfterLookup_zero18 c looked.here notLiteral not16 not17] at wait
          exact Or.inl ⟨regs, lookup_suffix_wait lookupRun wait⟩
        · rw [← clAfterLookup_zero18 c looked.here notLiteral not16 not17] at run
          obtain ⟨actual, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 run bound2 inv2
          refine Or.inr ⟨regs, state, used1 + used2, actual, bound, inv, ?_⟩
          rw [written]
          rw [List.drop_drop] at source2
          rw [source2, remaining2]
          exact tail
  rcases witness with wait | ⟨regs, state, used, actual, bound, inv, tail⟩
  · exact Or.inl wait
  · obtain ⟨result2, regs2, after2, used2, run2, _bound2, _inv2, _shape, _bits, post, _cursor, _budget⟩ :=
      clReadBody_run_cursor hr hc hz hs size mode stateInv more B
    rw [actual] at run2
    cases run2
    obtain ⟨observedState, heapEq, write⟩ := post
    have sameState : state = observedState := by
      have same := congrArg (fun heap : Heap => heap.istates zs) heapEq
      simp only [setI_istates_same] at same
      exact Option.some.inj same
    rw [← sameState] at write
    exact Or.inr ⟨regs, state, used, actual, bound, inv, write, tail⟩

#print axioms lookup_suffix_wait
#print axioms body_future
end Zlib.Inflate.Proofs.CodeLensFuture
