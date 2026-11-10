import ZlibF.Proof.«inflate.c.payload-future-loop-prefix»
import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»
import ZlibF.Proof.«inflate.c.fast-view-loop-byte-sizes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Attach the existing actual input budget, output range and byte-object
size frame to the same finite semantic loop execution. -/
theorem FastFutureReady.run_accounted
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (account : FastLoopInputBudget ctx startOff startBits q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExit ctx L D dict future tail target after result ∧
      FastLoopInputBudget ctx startOff startBits result ∧
      FastLoopOutputRange ctx after result ∧
      FastLoopInputLimit ctx result ∧ ByteViewSizes h after := by
  obtain ⟨result, after, run, semExit⟩ := semantic.run
  obtain ⟨other, otherAfter, otherRun, _, budget, output, limit⟩ :=
    semantic.toSafety.run_full_input_budget account
  have same : (result, after) = (other, otherAfter) :=
    Except.ok.inj (run.symm.trans otherRun)
  cases same
  have sizes : ByteViewSizes h after :=
    semantic.toSafety.byte_view_sizes_of_run run
  exact ⟨result, after, run, semExit, budget, output, limit, sizes⟩

/-- The loop-entry account is produced from the actual packet cursor.
No additional caller budget is needed. -/
theorem FastFutureReady.run_entry_accounted
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q) :
    ∃ startOff result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExit ctx L D dict future tail target after result ∧
      FastLoopInputBudget ctx startOff q.bits.toNat result ∧
      FastLoopOutputRange ctx after result ∧
      FastLoopInputLimit ctx result ∧ ByteViewSizes h after := by
  rcases semantic.toSafety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  have cursor : q.in_ = .ref ctx.inputRef off :=
    packet.cursor.trans nextPtr
  obtain ⟨result, after, run, semanticExit, budget, outputRange,
    inputLimit, sizes⟩ := semantic.run_accounted
      (FastLoopInputBudget.initial cursor)
  exact ⟨off, result, after, run, semanticExit, budget,
    outputRange, inputLimit, sizes⟩

#print axioms FastFutureReady.run_accounted
#print axioms FastFutureReady.run_entry_accounted
end Zlib.Inflate.Proofs
