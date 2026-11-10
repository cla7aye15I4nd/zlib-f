import ZlibF.Proof.«inflate.c.fast-committed-call-mode-v7»
import ZlibF.Proof.«inflate.c.fast-committed-output-segment»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- Every actual finite-loop observation, including a rejected final token,
records the physical bytes emitted before LOAD. -/
theorem FastCommittedCallCut.observation_segment
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (observation : Observation cut.p cut.loopHeap cut.result)
    (oldEq : cut.ready.state.tracked.history = current) :
    ∃ more : List UInt8,
      more.length = cut.made ∧
      writtenBytes cut.array (cut.ctx.oo + cut.made) cut.made = more ∧
      observation.history = current ++ more := by
  obtain ⟨inputArray, inputGet, inputBound, outputRange⟩ :=
    cut.ready.loop_source_geometry cut.loopRun
  obtain ⟨finalOff, loopArray, rangePtr, rangeLower,
    rangeUpper, loopGet, loopBound⟩ := outputRange
  have currentCtx : DefaultStateJ cut.finished cut.ctx.r cut.ctx.zs
      cut.zNext cut.sNext := by
    simpa only [cut.ctxR, cut.ctxZs] using cut.currentJ
  have suffixCursor :=
    (cut.ready.suffix_passive_frame cut.loopRun cut.suffixRun
      cut.entrySmall currentCtx).2
  have loadedPut : cut.loaded.put = cut.zNext.next_out := by
    rw [cut.loadedRegs, cut.regsShape]
  have finalPtr : cut.result.out =
      .ref cut.ctx.dest (cut.ctx.oo + cut.made) := by
    rw [← suffixCursor, ← loadedPut, cut.loadedPut, cut.ctxPut]
    rfl
  have finalOffEq : finalOff = cut.ctx.oo + cut.made :=
    (Ptr.ref.inj (rangePtr.symm.trans finalPtr)).2
  subst finalOff
  have Efinished : Env c cut.finished r zs cut.zNext cut.sNext :=
    ⟨cut.envStrm, cut.envState, cut.currentJ.good.live.hz,
      cut.currentJ.good.live.hs⟩
  have loadViews := inflateAfterFast_byte_views_of_run Efinished cut.loadRun
  have views := cut.ready.suffix_loaded_byte_views cut.loopRun cut.suffixRun
    cut.entrySmall loadViews
  have sameArray : cut.array = loopArray := Option.some.inj
    (cut.outputGet.symm.trans ((views cut.ctx.dest).trans loopGet))
  subst loopArray
  rcases cut.ready.state.safety with ⟨slow0, bs0, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, beforeGet, outputWrite, outputSize, current0,
    beginLe, span, guard⟩
  have initialPtr : cut.q.out = .ref cut.ctx.dest cut.ctx.oo :=
    cut.qOut.trans cut.ctxPut
  have oldCountBound : cut.ctx.oo - cut.ctx.bg ≤ cut.ctx.oo := Nat.sub_le _ _
  have oldBound : cut.ctx.oo ≤ output.size := by omega
  have newBound : cut.ctx.oo + cut.made ≤ cut.array.size := cut.outputBound
  have oldBytes : writtenBytes output cut.ctx.oo (cut.ctx.oo - cut.ctx.bg) =
      cut.ready.state.tracked.history :=
    cut.ready.state.tracked.historyView cut.ctx.oo output initialPtr beforeGet
  have oldLen : cut.ready.state.tracked.history.length = cut.ctx.oo - cut.ctx.bg := by
    rw [← oldBytes]
    simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
    have bgLe : cut.ctx.bg ≤ cut.ctx.oo := by
      rw [cut.ctx.beginEq]
      exact Nat.sub_le _ _
    omega
  have count : cut.ctx.oo + cut.made - cut.ctx.bg =
      (cut.ctx.oo - cut.ctx.bg) + cut.made := by
    have bgLe : cut.ctx.bg ≤ cut.ctx.oo := by
      rw [cut.ctx.beginEq]
      exact Nat.sub_le _ _
    omega
  have whole := observation.historyView (cut.ctx.oo + cut.made)
    cut.array finalPtr ((views cut.ctx.dest).symm.trans cut.outputGet)
  rw [count] at whole
  have localFrame : BufferFrame cut.restored cut.loadedHeap
      (fun b => StreamRoot cut.ctx.r b ∨ b = cut.ctx.zs)
      [⟨.ref cut.ctx.dest cut.ctx.oo, cut.made⟩] := by
    simpa only [cut.ctxR, cut.ctxZs, ← cut.ctxPut] using cut.frame
  obtain ⟨more, length, bytes, append⟩ :=
    fast_segment_of_whole localFrame beforeGet cut.outputGet
      oldCountBound oldBound newBound oldLen oldBytes whole
  exact ⟨more, length, bytes, by simpa only [oldEq] using append⟩

#print axioms FastCommittedCallCut.observation_segment
end Zlib.Inflate.Proofs.FunctionalEpoch
