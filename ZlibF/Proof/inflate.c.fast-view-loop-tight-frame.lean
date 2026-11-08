import ZlibF.Proof.«inflate.c.fast-view-loop-body-tight-frame»
import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

private theorem singleton_frame_refl
    {h : Heap} {dest : BRef} {off capacity : Nat}
    {array : Array UInt8} {changed : Nat → Prop}
    (get : Space.get h dest = some array)
    (write : Space.ro h dest = false) :
    BufferFrame h h changed [⟨.ref dest off, capacity⟩] := by
  have restored : restoreRegions h h
      [⟨.ref dest off, capacity⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil, get]
    exact byte_view_put_self get write
  refine ⟨?_, ?_⟩
  · rw [restored]
    simp only [Frame, Nat.le_refl, true_and]
    intro b live outside
    repeat' constructor <;> rfl
  · intro region member ref start beforeArray pointer beforeGet
    have same : region = ⟨.ref dest off, capacity⟩ := by
      simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref dest off = Ptr.ref ref start := pointer
    cases ptr
    exact ⟨beforeArray, beforeGet, rfl, fun _ _ _ => rfl⟩

/-- The actual whole fast loop preserves the original caller output
interval, including every broken exit. -/
theorem FastLoopReady.run_tight_frame
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      BufferFrame h after
        (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
        [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] ∧
      Shape h after ∧ Space.ro after ctx.dest = false := by
  let Changed : Nat → Prop := fun b => StreamRoot ctx.r b ∨ b = ctx.zs
  let Region : List Region := [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩]
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady ctx heap current ∧
      BufferFrame h heap Changed Region ∧ Shape h heap ∧
      Space.ro heap ctx.dest = false
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      BufferFrame h heap Changed Region ∧ Shape h heap ∧
      Space.ro heap ctx.dest = false
  have firstGet : ∃ array, Space.get h ctx.dest = some array := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact ⟨output, outputGet⟩
  obtain ⟨array, get⟩ := firstGet
  have firstWrite : Space.ro h ctx.dest = false := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact outputWrite
  have initial : Inv q h :=
    ⟨ready, singleton_frame_refl get firstWrite,
      Shape.refl h, firstWrite⟩
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
    obtain ⟨readyNow, accumulated, shapeAccum, writeCurrent⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨bodyFrame, shapeStep, writeAfter⟩ :=
      readyNow.body_tight_frame bodyRun
    have composed : BufferFrame h after Changed Region := by
      exact BufferFrame.singleton_trans accumulated bodyFrame
        shapeAccum get writeCurrent writeAfter
    have shapeFinal : Shape h after := shapeAccum.trans shapeStep
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1,
        stopped.2, composed, shapeFinal, writeAfter⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, composed, shapeFinal, writeAfter⟩,
        continuing.2.2⟩
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
        step initial fuelBound)
  exact ⟨result, after, run, final⟩

#print axioms FastLoopReady.run_tight_frame

end Zlib.Inflate.Proofs
