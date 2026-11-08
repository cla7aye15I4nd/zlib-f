import ZlibF.Proof.«inflate.c.fast-view-loop-body-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-exact-frame-bridge»
import ZlibF.Proof.«inflate.c.fast-view-loop-tight-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast loop changes bytes only up to its returned output cursor. -/
theorem FastLoopReady.run_exact_frame
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after k,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      result.out = .ref ctx.dest k ∧ ctx.oo ≤ k ∧
      k ≤ ctx.oo + ctx.leftTotal.toNat ∧
      BufferFrame h after
        (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] ∧
      Shape h after ∧ Space.ro after ctx.dest = false := by
  let Changed : Nat → Prop := fun b =>
    StreamRoot ctx.r b ∨ b = ctx.zs
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady ctx heap current ∧
      ∃ j, current.out = .ref ctx.dest j ∧ ctx.oo ≤ j ∧
        BufferFrame h heap Changed
          [⟨.ref ctx.dest ctx.oo, j - ctx.oo⟩] ∧
        Shape h heap ∧ Space.ro heap ctx.dest = false
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      ∃ j, current.out = .ref ctx.dest j ∧ ctx.oo ≤ j ∧
        j ≤ ctx.oo + ctx.leftTotal.toNat ∧
        BufferFrame h heap Changed
          [⟨.ref ctx.dest ctx.oo, j - ctx.oo⟩] ∧
        Shape h heap ∧ Space.ro heap ctx.dest = false
  have firstGet : ∃ array, Space.get h ctx.dest = some array := by
    rcases ready with ⟨slow, bs, output, off, j, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact ⟨output, outputGet⟩
  obtain ⟨array, get⟩ := firstGet
  have initial : Inv q h := by
    rcases ready with ⟨slow, bs, output, off, j, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact ⟨FastLoopReady.intro slow bs output off j packet
      invariant buffers codesGet distGet bitsBound leftEq outEq
      putPtr nextPtr lastPtr inputMargin outPtr outputGet outputWrite
      outputSize current beginLe span guard,
      j, outPtr, current,
      BufferFrame.singleton_refl outputGet outputWrite,
      Shape.refl h, outputWrite⟩
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
    obtain ⟨readyNow, jOld, outOld, lowerOld,
      accumulated, shapeAccum, writeCurrent⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨jInput, k, outInput, outResult, lowerInput,
      monotone, upper, bodyFrame, shapeStep, writeAfter⟩ :=
      readyNow.body_exact_frame bodyRun
    have jEq : jInput = jOld :=
      (Ptr.ref.inj (outInput.symm.trans outOld)).2
    subst jInput
    have widened : BufferFrame h heap Changed
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] :=
      BufferFrame.singleton_widen accumulated (by omega) (by omega)
    have composed : BufferFrame h after Changed
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] :=
      BufferFrame.singleton_trans widened bodyFrame
        shapeAccum get writeCurrent writeAfter
    have shapeFinal : Shape h after := shapeAccum.trans shapeStep
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1,
        stopped.2, k, outResult, (by omega), upper,
        composed, shapeFinal, writeAfter⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, k, outResult, (by omega),
          composed, shapeFinal, writeAfter⟩,
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
      (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx)
        Final step initial fuelBound)
  obtain ⟨exit, k, out, lower, upper, frame, shape, write⟩ := final
  exact ⟨result, after, k, run, exit, out, lower,
    upper, frame, shape, write⟩

#print axioms FastLoopReady.run_exact_frame

end Zlib.Inflate.Proofs
