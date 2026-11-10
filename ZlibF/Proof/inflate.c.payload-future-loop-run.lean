import ZlibF.Proof.«inflate.c.payload-future-loop-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

/-- The actual fast loop terminates on synchronized valid symbols. The last
body has a concrete token step and either a continuation parser or an EOB
witness; this theorem does not assert the whole public inflate call. -/
theorem FastFutureReady.run
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExit ctx L D dict future tail target after result := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastFutureReady ctx L D dict future tail target heap current
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastFutureExit ctx L D dict future tail target heap current
  have step : ∀ current heap, Inv current heap →
      ∃ result after,
        Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2,
          fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2,
          fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          Inv next heap2 ∧
          fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨result, after, bodyRun, outcome⟩ := state.step
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2⟩
    · exact Or.inr ⟨result, after, continuing.1,
        continuing.2.1, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases semantic.toSafety with ⟨slow, bs, output, off, k,
      packet, invariant, buffers, codesGet, distGet, bitsBound,
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
        step semantic fuelBound)
  exact ⟨result, after, run, final⟩

#print axioms FastFutureReady.run
end Zlib.Inflate.Proofs
