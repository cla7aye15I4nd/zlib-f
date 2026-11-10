import ZlibF.Proof.«inflate.c.fast-future-callee-join»
import ZlibF.Proof.«inflate.c.fast-view-writeback-output-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Actual fast suffix stores the semantic loop's physical output cursor.
The input size and rollback obligations are derived from the same entry
packet and the checked loop, with no extra caller buffer restriction. -/
theorem FastFutureReady.writeback_output_cursor
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h after finished : Heap} {q result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (smallBits : q.bits.toNat < 8)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) after =
      .ok ((), finished))
    (current : DefaultStateJ finished ctx.r ctx.zs zNext sNext) :
    zNext.next_out = result.out := by
  rcases semantic.toSafety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, currentOut,
    beginLe, span, guard⟩
  have cursor : q.in_ = .ref ctx.inputRef off :=
    packet.cursor.trans nextPtr
  obtain ⟨other, otherAfter, otherRun, exit, budget,
    outputRange, inputLimit, sizes⟩ := semantic.run_accounted
      (FastLoopInputBudget.initial cursor)
  have same : (result, after) = (other, otherAfter) :=
    Except.ok.inj (loopRun.symm.trans otherRun)
  cases same
  obtain ⟨inputBefore, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨inputAfter, afterGet, sizeEq⟩ := sizes.view beforeGet
  have inputBound : off + slow.have_.toNat ≤ inputAfter.size := by
    omega
  exact exit.1.writeback_output_cursor budget inputLimit outputRange
    smallBits lastPtr inputMargin (UInt32.toNat_lt slow.have_)
    afterGet inputBound suffixRun current

#print axioms FastFutureReady.writeback_output_cursor
end Zlib.Inflate.Proofs
