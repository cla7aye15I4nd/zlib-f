import ZlibF.Proof.«inflate.c.local-fast-exact-output-loop-body»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

theorem FastLoopReady.run_exact_output
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady cutoff ctx h q) :
    ∃ result after k,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit cutoff ctx after result ∧
      result.out = .ref ctx.dest k ∧ ctx.oo ≤ k ∧
      k ≤ ctx.oo + ctx.leftTotal.toNat ∧
      BufferFrame h after
        (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] ∧
      FastMemoryMetaFrame ctx.r h after ∧ Space.ro after ctx.dest = false := by
  let Changed : Nat → Prop := fun b =>
    StreamRoot ctx.r b ∨ b = ctx.zs
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady cutoff ctx heap current ∧
      ∃ j, current.out = .ref ctx.dest j ∧ ctx.oo ≤ j ∧
        BufferFrame h heap Changed
          [⟨.ref ctx.dest ctx.oo, j - ctx.oo⟩] ∧
        FastMemoryMetaFrame ctx.r h heap ∧ Space.ro heap ctx.dest = false
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit cutoff ctx heap current ∧
      ∃ j, current.out = .ref ctx.dest j ∧ ctx.oo ≤ j ∧
        j ≤ ctx.oo + ctx.leftTotal.toNat ∧
        BufferFrame h heap Changed
          [⟨.ref ctx.dest ctx.oo, j - ctx.oo⟩] ∧
        FastMemoryMetaFrame ctx.r h heap ∧ Space.ro heap ctx.dest = false
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
      FastMemoryMetaFrame.refl ctx.r h, outputWrite⟩
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
      accumulated, memoryAccum, writeCurrent⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨jInput, k, outInput, outResult, lowerInput,
      monotone, upper, bodyFrame⟩ :=
      readyNow.body_exact_output bodyRun
    have memoryStep := fastMemoryMetaFrameM_fast_body ctx.r ctx.c ctx.streamPtr current heap result after bodyRun
    have allMemory := memoryAccum.trans memoryStep
    have writeAfter : Space.ro after ctx.dest = false :=
      (fast_memory_readonly memoryStep ctx.dest).trans writeCurrent
    have jEq : jInput = jOld :=
      (Ptr.ref.inj (outInput.symm.trans outOld)).2
    subst jInput
    have widened : BufferFrame h heap Changed
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] :=
      BufferFrame.singleton_widen accumulated (by omega) (by omega)
    have composed : BufferFrame h after Changed
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] :=
      BufferFrame.singleton_trans_live widened bodyFrame
        (fast_memory_live memoryAccum) get writeCurrent writeAfter

    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1,
        stopped.2, k, outResult, (by omega), upper,
        composed, allMemory, writeAfter⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, k, outResult, (by omega),
          composed, allMemory, writeAfter⟩,
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

#print axioms FastLoopReady.run_exact_output
end Zlib.Inflate.Local
