import ZlibF.Proof.«inflate.c.fast-future-writeback-byte-views»
import ZlibF.Proof.«inflate.c.fast-future-writeback-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

theorem FastFutureReady.writeback_byte_views
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h after finished : Heap} {q result : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (smallBits : q.bits.toNat < 8)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) after =
      .ok ((), finished))
    :
    ∀ ref : BRef, Space.get finished ref = Space.get after ref := by
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
  exact exit.1.writeback_byte_views_of_run budget inputLimit outputRange
    smallBits lastPtr inputMargin (UInt32.toNat_lt slow.have_)
    afterGet inputBound suffixRun

#print axioms FastFutureReady.writeback_byte_views
end Zlib.Inflate.Proofs
