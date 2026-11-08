import ZlibF.Proof.«inflate.c.fast-view-loop-broke-entry»
import ZlibF.Proof.«inflate.c.fast-view-body-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-entry-loop-budget»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A body entered with a clear break flag can set it only through the
actual BAD or TYPE source branch. -/
theorem FastLoopReady.body_break_cause
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (clear : q.broke = false)
    (run : C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
      .ok (result, after))
    (broken : result.broke = true) :
    (∃ i, after = badHeap h ctx.r ctx.zs ctx.z ctx.s i) ∨
      after = setI h ctx.zs { ctx.s with mode := TYPE } := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth,
    rest, rfl⟩ := packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  obtain ⟨slowFinal, bodyResult, bodyAfter, bodyRun,
    effect, _⟩ :=
    packet.fast_body_break_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have same : (bodyResult, bodyAfter) = (result, after) :=
    Except.ok.inj (bodyRun.symm.trans run)
  cases same
  rcases effect with ⟨sameBreak, _⟩ | ⟨i, broke, heapEq⟩ | heapEq
  · rw [clear] at sameBreak
    rw [sameBreak] at broken
    cases broken
  · exact Or.inl ⟨i, heapEq⟩
  · exact Or.inr heapEq

/-- Reading the final decoder record turns an actual BAD or TYPE source
heap update into a final mode fact. -/
theorem FastLoopExit.broken_mode_of_cause
    {ctx : FastLoopContext} {h before : Heap}
    {q : Zlib.Inffast.L}
    (final : FastLoopExit ctx h q)
    (cause : (∃ i, h = badHeap before ctx.r ctx.zs ctx.z ctx.s i) ∨
      h = setI before ctx.zs { ctx.s with mode := TYPE }) :
    ∃ zNext sNext,
      DefaultStateJ h ctx.r ctx.zs zNext sNext ∧
      (sNext.mode = BAD ∨ sNext.mode = TYPE) := by
  obtain ⟨slow, bs, zNext, sNext, packet, current, buffers⟩ := final
  refine ⟨zNext, sNext, current, ?_⟩
  rcases cause with ⟨i, heapEq⟩ | heapEq
  · have hs := current.good.live.hs
    rw [heapEq] at hs
    simp only [badHeap, setI_istates_same] at hs
    have same := Option.some.inj hs.symm
    exact Or.inl (by simpa using congrArg InflateState.mode same)
  · have hs := current.good.live.hs
    rw [heapEq] at hs
    simp only [setI_istates_same] at hs
    have same := Option.some.inj hs.symm
    exact Or.inr (by simpa using congrArg InflateState.mode same)

/-- Starting from the actual clear break flag, a broken complete fast loop
must leave the decoder in BAD or TYPE mode. -/
theorem FastLoopReady.run_broken_mode
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (clear : q.broke = false) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = true →
        ∃ zNext sNext,
          DefaultStateJ after ctx.r ctx.zs zNext sNext ∧
          (sNext.mode = BAD ∨ sNext.mode = TYPE)) := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady ctx heap current ∧ current.broke = false
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      (current.broke = true →
        ∃ zNext sNext,
          DefaultStateJ heap ctx.r ctx.zs zNext sNext ∧
          (sNext.mode = BAD ∨ sNext.mode = TYPE))
  have step : ∀ current heap, Inv current heap →
      ∃ result after,
        Zlib.Inffast.inflate_fast_body ctx.c current heap =
          .ok (result, after) ∧
        ((∃ next heap2,
            fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
            Final next heap2) ∨
         (∃ next heap2,
            fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
            Inv next heap2 ∧
            fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨readyNow, clearNow⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · refine Or.inl ⟨result, after, stopped.1,
        stopped.2, ?_⟩
      intro broken
      exact stopped.2.broken_mode_of_cause
        (readyNow.body_break_cause clearNow bodyRun broken)
    · have clearResult : result.broke = false :=
        fastLoopCond_true_not_broken continuing.1
      exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, clearResult⟩, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx) Final
        step ⟨ready, clear⟩ fuelBound)
  exact ⟨result, after, run, final⟩

/-- The exact fast prefix supplies the clear flag consumed by the loop
mode proof. This uses the same actual prefix and loop runs as rollback. -/
theorem fastEntryLoop_run_broken_mode
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ ctx initial result after,
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, initial), h) ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = true →
        ∃ zNext sNext,
          DefaultStateJ after ctx.r ctx.zs zNext sNext ∧
          (sNext.mode = BAD ∨ sNext.mode = TYPE)) := by
  obtain ⟨ctx, initial, result, after, startOff, off, used,
    input, prefixRun, sameR, sameZs, startCursor, initialBits,
    ready, loopRun, final, budget, output, limit, resultCursor,
    inputGet, usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_rollback invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨clearCtx, clearInitial, clearRun, clearReady,
    clear⟩ :=
    fastEntryPrefix_ready_not_broken invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have samePrefix := Except.ok.inj (clearRun.symm.trans prefixRun)
  have sameInitial : clearInitial = initial := by
    exact congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap =>
      p.1.2) samePrefix
  have clearActual : initial.broke = false := by
    rw [← sameInitial]
    exact clear
  obtain ⟨modeResult, modeAfter, modeRun, modeFinal,
    modePost⟩ := ready.run_broken_mode clearActual
  have sameLoop : (modeResult, modeAfter) = (result, after) :=
    Except.ok.inj (modeRun.symm.trans loopRun)
  cases sameLoop
  exact ⟨ctx, initial, result, after, prefixRun, loopRun,
    final, modePost⟩

#print axioms FastLoopReady.body_break_cause
#print axioms FastLoopExit.broken_mode_of_cause
#print axioms FastLoopReady.run_broken_mode
#print axioms fastEntryLoop_run_broken_mode

end Zlib.Inflate.Proofs
