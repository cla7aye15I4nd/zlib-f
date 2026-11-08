import ZlibF.Proof.«inflate.c.fast-view-loop-broke-entry»
import ZlibF.Proof.«inflate.c.fast-view-body-break-effect»

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

#print axioms FastLoopReady.body_break_cause
#print axioms FastLoopExit.broken_mode_of_cause
#print axioms FastLoopReady.run_broken_mode

end Zlib.Inflate.Proofs
