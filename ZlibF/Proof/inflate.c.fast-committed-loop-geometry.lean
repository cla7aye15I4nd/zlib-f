import ZlibF.Proof.«inflate.c.fast-committed-exit-source»
import ZlibF.Proof.«inflate.c.fast-view-loop-byte-sizes»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual finite loop's safety witness transports the original input
array extent to the final heap and retains output bounds for source rollback.
The raw count is identified by fixed `last` pointer offsets, not by byte
contents, so repeated input bytes are harmless. -/
theorem WordReady.loop_source_geometry
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h after : Heap} {q result : Zlib.Inffast.L}
    (ready : WordReady p h q)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    ∃ input : Array UInt8,
      Space.get after ctx.inputRef = some input ∧
      p.startOff + p.input.length ≤ input.size ∧
      FastLoopOutputRange ctx after result := by
  have currentCursor : ∃ off, q.in_ = .ref ctx.inputRef off := by
    rcases ready.state.safety with ⟨slow, bs, output, off, k,
      packet, invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact ⟨off, packet.cursor.trans nextPtr⟩
  obtain ⟨currentOff, currentCursor⟩ := currentCursor
  obtain ⟨other, otherHeap, otherRun, _final, _account,
    outputRange, _limit⟩ :=
    ready.state.safety.run_full_input_budget
      (FastLoopInputBudget.initial currentCursor)
  have same : (result, after) = (other, otherHeap) :=
    Except.ok.inj (loopRun.symm.trans otherRun)
  cases same
  have sizes := ready.state.safety.byte_view_sizes_of_run loopRun
  rcases ready.state.safety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨beforeInput, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨afterInput, afterGet, sizeEq⟩ := sizes.view beforeGet
  have endpoint : off + slow.have_.toNat =
      p.startOff + p.input.length := by
    have lastSame := (Ptr.ref.inj (lastPtr.symm.trans p.initialLast)).2
    have margin := p.rawMargin
    omega
  refine ⟨afterInput, afterGet, ?_, outputRange⟩
  rw [sizeEq, ← endpoint]
  exact beforeBound

#print axioms WordReady.loop_source_geometry
end Zlib.Inflate.Proofs.FastCommittedLoop
