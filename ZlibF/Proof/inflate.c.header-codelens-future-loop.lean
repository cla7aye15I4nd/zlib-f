import ZlibF.Proof.«inflate.c.header-codelens-future-body»
namespace Zlib.Inflate.Proofs.CodeLensFuture
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CodeLensCompletion
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Exhaustive actual reader classification on a valid cumulative future
CodeLens derivation. Invalid exits and BAD are excluded by syntax; neither
leave nor a returned CODELENS mode is supplied by the caller. -/
theorem clRead_future
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet out : List Nat} {future rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs ++ future) rest out) :
    ∃ outcome regs state used,
      runX (clRead c) l h = .ok ((outcome, regs), setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
      (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ state.«have».toNat = s.nlen.toNat + s.ndist.toNat ∧
          stream regs (bs.drop used) ++ future = rest ∧ actualLengthPrefix state = out)) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    CodeLens alphabet total (actualLengthPrefix state) (stream regs (bs.drop used) ++ future) rest out
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun outcome regs after =>
    ∃ state used, after = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
      (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.«have».toNat = total ∧
        stream regs (bs.drop used) ++ future = rest ∧ actualLengthPrefix state = out))
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, state, used, heapEq, frame, sz, count, values, bound, inv, outcomeKind⟩ := loop
    subst after
    exact ⟨outcome, regs, state, used, by rw [clRead_eq]; exact run, frame, sz, count, values, bound, inv, outcomeKind⟩
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, remainingParsed⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have currentStream : r.get (setI h zs state) = some z := by simpa using hz
    have fields : state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.mode = CODELENS := by
      rw [frame]
      exact ⟨rfl, rfl, mode⟩
    have totalEq : state.nlen.toNat + state.ndist.toNat = total := by rw [fields.1, fields.2.1]
    have sum : (state.nlen + state.ndist).toNat = total := by
      rw [fields.1, fields.2.1, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have currentInv : CodeLengthInvariant zs state := by
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
      · rw [frame]; exact pointer
      · rw [frame]; exact table
      · rw [fields.1]; exact nlen
      · rw [fields.2.1]; exact ndist
      · rw [totalEq]; exact count
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by
      rw [frame]
      exact contents
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have less := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at less
        rw [totalEq]
        exact less
      rw [← totalEq] at remainingParsed
      rcases body_future hr hc currentStream get sz fields.2.2 currentInv currentContents moreNat bitInv remainingParsed with wait | ⟨nextRegs, nextState, consumed, bodyRun, consumedBound, nextInv, write, nextParsed⟩
      · obtain ⟨nextRegs, bodyRun⟩ := wait
        obtain ⟨result0, regs0, heap0, consumed, run0, consumedBound, nextInv, _shape, _bits, _post, _cursor, _budget⟩ :=
          clReadBody_run_cursor hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv
        rw [bodyRun] at run0
        cases run0
        have consumedTotal : used + consumed ≤ bs.length := by
          simp only [List.length_drop] at consumedBound
          omega
        have remainder : (bs.drop used).drop consumed = bs.drop (used + consumed) := by simp only [List.drop_drop]
        rw [remainder] at nextInv
        refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
          .error Ex.leave, nextRegs, setI h zs state, bodyRun, state, used + consumed, rfl, frame, sz, count,
          prefixValues, consumedTotal, nextInv, Or.inl rfl⟩
      · obtain ⟨writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := write
        refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
          .ok false, nextRegs, setI (setI h zs state) zs nextState, bodyRun, ?_⟩
        have consumedTotal : used + consumed ≤ bs.length := by
          simp only [List.length_drop] at consumedBound
          omega
        have remainder : (bs.drop used).drop consumed = bs.drop (used + consumed) := by simp only [List.drop_drop]
        rw [totalEq, remainder] at nextParsed
        rw [remainder] at nextInv
        constructor
        · refine ⟨nextState, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix, consumedTotal, nextInv, nextParsed⟩
          · rw [writeFrame, frame]
          · rw [totalEq] at nextCount
            exact nextCount
        · dsimp only [rank]
          simp only [setI_istates_same, Option.getD_some]
          rw [totalEq] at nextCount
          omega
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      have prefixFull : (actualLengthPrefix state).length = total := (Zlib.Inftrees.Proofs.lensOf_length _ _).trans full
      obtain ⟨source, lens⟩ := parsed_full remainingParsed prefixFull
      refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun,
        state, used, rfl, frame, sz, count, prefixValues, usedBound, bitInv, Or.inr ⟨rfl, full, source, lens⟩⟩
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simpa only [List.drop_zero] using parsed⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

#print axioms clRead_future
end Zlib.Inflate.Proofs.CodeLensFuture
