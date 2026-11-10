import ZlibF.Proof.«inflate.c.dynamic-empty-body-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- The real ordinary loop preserves a reversible causal prefix on every surviving read and wait. -/
theorem clRead_empty_stream_source {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (root : s.lenbits.toNat=1) (first : s.codes[0]?=some (⟨64,1,0⟩:Code))
    (second : s.codes[1]?=some (⟨64,1,0⟩:Code))
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used)) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used consumed,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    stream l bs = consumed ++ stream regs (bs.drop used)
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun _ regs after => ∃ state used,
    after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
    (∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used))
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, state, used, get, bound, inv, trace⟩ := loop
    exact ⟨outcome, regs, after, state, used, by rw [clRead_eq]; exact run, get, bound, inv, trace⟩
  · intro regs heap inv
    obtain ⟨state, used, consumed, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, source⟩ := inv
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
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [frame]; exact contents
    have currentRoot : state.lenbits.toNat=1 := by rw [frame];exact root
    have currentFirst : state.codes[0]?=some (⟨64,1,0⟩:Code) := by rw [frame];exact first
    have currentSecond : state.codes[1]?=some (⟨64,1,0⟩:Code) := by rw [frame];exact second
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
      obtain ⟨result, nextRegs, after, usedStep, bodyRun, stepBound, nextInv, _shape, _bits, post, _cursor, _budget⟩ :=
        clReadBody_run_cursor hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv
      have totalBound : used + usedStep ≤ bs.length := by simp only [List.length_drop] at stepBound; omega
      have remainder : (bs.drop used).drop usedStep = bs.drop (used + usedStep) := by simp only [List.drop_drop]
      have nextInput : BitInv after nextRegs (bs.drop (used + usedStep)) := by rw [← remainder]; exact nextInv
      obtain ⟨emptyResult,emptyRegs,emptyHeap,emptyUsed,emptyRun,emptyBound,emptyInv,emptySource,emptyKinds⟩ :=
        empty_body_source hc get sz fields.2.2 currentInv currentRoot currentFirst currentSecond moreNat bitInv
      rw [bodyRun] at emptyRun
      cases emptyRun
      have emptyUsedEq : emptyUsed=usedStep := by
        have a:=emptyInv.have_eq;have b:=nextInv.have_eq
        simp only [List.length_drop] at a b emptyBound stepBound
        omega
      subst emptyUsed
      obtain ⟨bitsStep,stepSource⟩ := emptySource
      rw [remainder] at stepSource
      have combinedSource : stream l bs=(consumed++bitsStep)++stream nextRegs (bs.drop (used+usedStep)) := by
        rw [List.append_assoc,←stepSource]
        exact source
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      cases result with
      | error exit =>
        have heapSame : after = setI h zs state := post
        subst after
        exact ⟨state,used+usedStep,get,totalBound,nextInput,consumed++bitsStep,combinedSource⟩
      | ok decision =>
        cases decision with
        | true =>
          rcases emptyKinds with ⟨impossible,_⟩|⟨impossible,_⟩ <;> cases impossible
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          subst after
          constructor
          · refine ⟨nextState, used + usedStep, consumed ++ bitsStep, by simp, ?_, nextSize, ?_, nextPrefix,
              totalBound, ?_, combinedSource⟩
            · rw [writeFrame, frame]
            · rw [totalEq] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInput
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [totalEq] at nextCount
            omega
    · refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun,
        state, used, get, usedBound, bitInv, consumed, source⟩
  · exact ⟨s, 0, [], (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simp⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

#print axioms clRead_empty_stream_source
end Zlib.Inflate.Proofs.DynamicRejects
