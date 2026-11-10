import ZlibF.Proof.«inflate.c.fast-committed-callee-loaded-source-v2»
import ZlibF.Proof.«inflate.c.fast-future-writeback-byte-views»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast suffix and LOAD leave all byte views as they were at
finite-loop exit, including a caller input/output pair sharing one object. -/
theorem WordReady.suffix_loaded_byte_views
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h loopHeap finished loadedHeap : Heap}
    {q result : Zlib.Inffast.L}
    (ready : WordReady p h q)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, loopHeap))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) loopHeap =
      .ok ((), finished))
    (smallEntry : q.bits.toNat < 8)
    (loadViews : ∀ ref : BRef,
      Space.get loadedHeap ref = Space.get finished ref) :
    ∀ ref : BRef, Space.get loadedHeap ref = Space.get loopHeap ref := by
  rcases ready.state.safety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  have cursor : q.in_ = .ref ctx.inputRef off := packet.cursor.trans nextPtr
  have safety : FastLoopReady ctx h q :=
    ⟨slow, bs, output, off, k, packet, invariant, buffers,
      codesGet, distGet, bitsBound, leftEq, outEq,
      putPtr, nextPtr, lastPtr, inputMargin, outPtr,
      outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
  obtain ⟨other, otherHeap, otherRun, final,
    budget, outputRange, limit⟩ :=
    safety.run_full_input_budget (FastLoopInputBudget.initial cursor)
  have same : (result, loopHeap) = (other, otherHeap) :=
    Except.ok.inj (loopRun.symm.trans otherRun)
  cases same
  have sizes := safety.byte_view_sizes_of_run loopRun
  obtain ⟨beforeInput, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨afterInput, afterGet, sizeEq⟩ := sizes.view beforeGet
  have inputBound : off + slow.have_.toNat ≤ afterInput.size := by omega
  have suffixViews := final.writeback_byte_views_of_run budget limit
    outputRange smallEntry lastPtr inputMargin
    (UInt32.toNat_lt slow.have_) afterGet inputBound suffixRun
  intro ref
  exact (loadViews ref).trans (suffixViews ref)

#print axioms WordReady.suffix_loaded_byte_views
end Zlib.Inflate.Proofs.FastCommittedLoop
