import ZlibF.Proof.«inflate.c.fast-committed-call-cut-v7»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
set_option autoImplicit false

/-- The actual suffix changes held bits and LOAD may change `back`; neither
changes the mode chosen by the real body loop. -/
theorem FastCommittedCallCut.loaded_mode_of_loop_j
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    {loopZ : ZStream} {loopS : InflateState}
    (loopJ : DefaultStateJ cut.loopHeap cut.ctx.r cut.ctx.zs loopZ loopS) :
    cut.loadedState.mode = loopS.mode := by
  rcases cut.ready.state.safety with ⟨slow0, bs0, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  have cursor : cut.q.in_ = .ref cut.ctx.inputRef off := packet.cursor.trans nextPtr
  have safety : FastLoopReady cut.ctx cut.restored cut.q :=
    ⟨slow0, bs0, output, off, k, packet, invariant, buffers,
      codesGet, distGet, bitsBound, leftEq, outEq,
      putPtr, nextPtr, lastPtr, inputMargin, outPtr,
      outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
  obtain ⟨other, otherHeap, otherRun, final,
    budget, outputRange, limit⟩ :=
    safety.run_full_input_budget (FastLoopInputBudget.initial cursor)
  have same : (cut.result, cut.loopHeap) = (other, otherHeap) :=
    Except.ok.inj (cut.loopRun.symm.trans otherRun)
  cases same
  have sizes := safety.byte_view_sizes_of_run cut.loopRun
  obtain ⟨beforeInput, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨afterInput, afterGet, sizeEq⟩ := sizes.view beforeGet
  have inputBound : off + slow0.have_.toNat ≤ afterInput.size := by omega
  obtain ⟨otherFinished, otherZ, otherS, zBefore, sBefore,
    otherSuffix, beforeJ, afterJ, suffixFields⟩ :=
    final.writeback_state_core_frame budget limit outputRange
      cut.entrySmall
      lastPtr inputMargin (UInt32.toNat_lt slow0.have_)
      afterGet inputBound
  have sameSuffix : cut.finished = otherFinished := by
    have pair := Except.ok.inj (cut.suffixRun.symm.trans otherSuffix)
    exact congrArg Prod.snd pair
  subst otherFinished
  have sameZ : cut.zNext = otherZ := Option.some.inj
    (cut.currentJ.good.live.hz.symm.trans (by simpa only [cut.ctxR] using afterJ.good.live.hz))
  have sameS : cut.sNext = otherS := Option.some.inj
    (cut.currentJ.good.live.hs.symm.trans (by simpa only [cut.ctxZs] using afterJ.good.live.hs))
  subst otherZ; subst otherS
  have sameBefore : sBefore = loopS := Option.some.inj
    (beforeJ.good.live.hs.symm.trans loopJ.good.live.hs)
  have Efinished : Env c cut.finished r zs cut.zNext cut.sNext :=
    ⟨cut.envStrm, cut.envState, cut.currentJ.good.live.hz, cut.currentJ.good.live.hs⟩
  have loadCore := inflateAfterFast_state_core_frame Efinished cut.loadRun cut.finalJ
  rw [loadCore, suffixFields, sameBefore]

/-- Actual normal, EOB and BAD word exits match the mode loaded by the
caller. The three certificates are the same finite-loop result. -/
theorem FastCommittedCallCut.loaded_mode_cases
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current) :
    (∃ tracked : Tracked cut.p cut.loopHeap cut.result,
      WordSource tracked.toObservation ∧ cut.loadedState.mode = s.mode) ∨
    (∃ ended : Ended cut.p cut.loopHeap cut.result,
      WordSource ended.toObservation ∧ cut.loadedState.mode = TYPE) ∨
    (∃ rejected : RejectedObservation cut.p cut.loopHeap cut.result,
      WordSource rejected.toObservation ∧ cut.loadedState.mode = BAD) := by
  rcases cut.rejectedExit.2 with normal | eob | bad
  · obtain ⟨tracked, source, loopJ⟩ := normal
    have mode := cut.loaded_mode_of_loop_j loopJ
    refine Or.inl ⟨tracked, source, ?_⟩
    simpa only [cut.ctxS, leaveState] using mode
  · obtain ⟨ended, source⟩ := eob
    have mode := cut.loaded_mode_of_loop_j ended.state
    exact Or.inr (Or.inl ⟨ended, source, by simpa only using mode⟩)
  · obtain ⟨rejected, source⟩ := bad
    obtain ⟨i, loopJ⟩ := rejected.state
    have mode := cut.loaded_mode_of_loop_j loopJ
    exact Or.inr (Or.inr ⟨rejected, source, by simpa only using mode⟩)

#print axioms FastCommittedCallCut.loaded_mode_of_loop_j
#print axioms FastCommittedCallCut.loaded_mode_cases
end Zlib.Inflate.Proofs.FunctionalEpoch
