import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every actual fast body retains all represented byte-object sizes,
including its state and stream stores on broken exits. -/
theorem FastLoopReady.body_byte_view_sizes
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ByteViewSizes h after := by
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
    array, next, _, _, run, _, _, _, sizes, _⟩ :=
    packet.fast_body_view_post invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  exact ⟨result, after, run, sizes⟩

/-- All byte-object size equalities compose across the actual complete
fast loop. This includes its final broken body and condition. -/
theorem FastLoopReady.run_with_byte_view_sizes
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧ ByteViewSizes h after := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady ctx heap current ∧ ByteViewSizes h heap
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧ ByteViewSizes h heap
  have step : ∀ current heap, Inv current heap →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          Inv next heap2 ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨readyNow, priorSizes⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨sizeResult, sizeAfter, sizeRun, bodySizes⟩ := readyNow.body_byte_view_sizes
    have same : (result, after) = (sizeResult, sizeAfter) :=
      Except.ok.inj (bodyRun.symm.trans sizeRun)
    cases same
    have sizes : ByteViewSizes h after := priorSizes.trans bodySizes
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, sizes⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, sizes⟩, continuing.2.2⟩
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
        step ⟨ready, ByteViewSizes.refl h⟩ fuelBound)
  exact ⟨result, after, run, final⟩

/-- The size frame is attached to a given actual loop run, so a caller can
combine it with the input ledger without choosing a second execution. -/
theorem FastLoopReady.byte_view_sizes_of_run
    {ctx : FastLoopContext} {h after : Heap} {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    ByteViewSizes h after := by
  obtain ⟨found, foundAfter, foundRun, _, sizes⟩ := ready.run_with_byte_view_sizes
  have same : (result, after) = (found, foundAfter) := Except.ok.inj (run.symm.trans foundRun)
  have equal : after = foundAfter := congrArg Prod.snd same
  rw [equal]
  exact sizes

#print axioms FastLoopReady.body_byte_view_sizes
#print axioms FastLoopReady.run_with_byte_view_sizes
#print axioms FastLoopReady.byte_view_sizes_of_run
end Zlib.Inflate.Proofs
