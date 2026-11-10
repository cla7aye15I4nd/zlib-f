import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual default fast loop returns without a fault or fuel exhaustion
from an established fast-call entry and retains the decoder and buffers. -/
theorem FastLoopReady.run
    {ctx : FastLoopContext} {h : Heap} {l : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h l) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) l) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result := by
  have hstep : ∀ q hh, FastLoopReady ctx hh q →
      ∃ result after,
        Zlib.Inffast.inflate_fast_body ctx.c q hh =
          .ok (result, after) ∧
        ((∃ q2 hh2,
          fastLoopCond ctx result after =
            .ok ((false, q2), hh2) ∧
          FastLoopExit ctx hh2 q2) ∨
         (∃ q2 hh2,
          fastLoopCond ctx result after =
            .ok ((true, q2), hh2) ∧
          FastLoopReady ctx hh2 q2 ∧
          fastLoopMeasure ctx q2 < fastLoopMeasure ctx q)) := by
    intro q hh state
    obtain ⟨result, after, run, outcome⟩ := state.step
    exact ⟨result, after, run, outcome.elim
      (fun ⟨condition, final⟩ =>
        Or.inl ⟨result, after, condition, final⟩)
      (fun ⟨condition, next, decrease⟩ =>
        Or.inr ⟨result, after, condition, next, decrease⟩)⟩
  have hfuel : fastLoopMeasure ctx l < fuel := by
    rcases ready with ⟨slow, bs, output, off, k,
      packet, invariant, buffers, codesGet, distGet,
      bitsBound, leftEq, outEq, putPtr, nextPtr,
      lastPtr, inputMargin, outPtr, outputGet,
      outputWrite, outputSize, current, beginLe, span,
      guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile
        (fun q hh => FastLoopReady ctx hh q)
        (fastLoopMeasure ctx)
        (fun q hh => FastLoopExit ctx hh q)
        hstep ready hfuel)
  refine ⟨result, after, ?_, final⟩
  have condEq : fastLoopCond ctx =
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) := by
    funext q
    rfl
  rw [condEq] at run
  exact run

end Zlib.Inflate.Proofs
