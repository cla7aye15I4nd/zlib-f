import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»
import ZlibF.Proof.«inflate.c.fast-view-body-bounded-progress-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every actual body either breaks or advances output strictly beyond
the original fast-call output cursor. -/
theorem FastLoopReady.body_output_progress
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      (result.broke = true ∨ ∃ off, result.out = .ref ctx.dest off ∧ ctx.oo < off) := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by rw [leftEq]; exact ctx.endPtr
  obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
    usedBound, consumedBound, run, packetNext, invariantNext,
    buffersNext, sizes, streamEq, progress⟩ :=
    packet.fast_body_bounded_progress_default_state invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  refine ⟨result, after, run, ?_⟩
  rcases progress with broke | ⟨next, cursor, strict, upper⟩
  · exact Or.inl broke
  · exact Or.inr ⟨next, cursor, by omega⟩

/-- The complete actual loop either takes a source break or produces at
least one byte. The conclusion includes its final false condition. -/
theorem FastLoopReady.run_with_output_progress
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = true ∨ ∃ off, result.out = .ref ctx.dest off ∧ ctx.oo < off) := by
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      (current.broke = true ∨ ∃ off, current.out = .ref ctx.dest off ∧ ctx.oo < off)
  have step : ∀ current heap, FastLoopReady ctx heap current →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          FastLoopReady ctx heap2 next ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap currentReady
    obtain ⟨result, after, run, outcome⟩ := currentReady.step
    obtain ⟨progressResult, progressAfter, progressRun, progress⟩ :=
      currentReady.body_output_progress
    have same : (result, after) = (progressResult, progressAfter) :=
      Except.ok.inj (run.symm.trans progressRun)
    cases same
    refine ⟨result, after, run, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, progress⟩
    · exact Or.inr ⟨result, after, continuing⟩
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
      (Zlib.Inffast.Proofs.Wp.cdoWhile (fun current heap => FastLoopReady ctx heap current)
        (fastLoopMeasure ctx) Final step ready fuelBound)
  exact ⟨result, after, run, final⟩

/-- Attach output progress to the exact loop result already in use. -/
theorem FastLoopReady.output_progress_of_run
    {ctx : FastLoopContext} {h after : Heap} {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    result.broke = true ∨ ∃ off, result.out = .ref ctx.dest off ∧ ctx.oo < off := by
  obtain ⟨found, foundAfter, foundRun, final, progress⟩ := ready.run_with_output_progress
  have same : (result, after) = (found, foundAfter) :=
    Except.ok.inj (run.symm.trans foundRun)
  cases same
  exact progress

#print axioms FastLoopReady.body_output_progress
#print axioms FastLoopReady.run_with_output_progress
#print axioms FastLoopReady.output_progress_of_run
end Zlib.Inflate.Proofs
