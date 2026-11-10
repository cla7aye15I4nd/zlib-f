import ZlibF.Proof.«inflate.c.fast-committed-load-passive»
import ZlibF.Proof.«inflate.c.fast-committed-byte-views»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- The actual finite fast loop and its suffix preserve the passive decoder,
checksum, and allocator fields. The proof follows the exact loop and suffix
run, including BAD and TYPE, with no parser future premise. -/
theorem WordReady.suffix_passive_frame
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h loopHeap finished : Heap} {q result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState}
    (ready : WordReady p h q)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, loopHeap))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) loopHeap =
      .ok ((), finished))
    (smallEntry : q.bits.toNat < 8)
    (finalJ : DefaultStateJ finished ctx.r ctx.zs zNext sNext) :
    FastPassiveFrame ctx.z zNext ctx.s sNext ∧
    zNext.next_out = result.out := by
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
  have loopFields := safety.scalar_frame_of_run loopRun
  have sizes := safety.byte_view_sizes_of_run loopRun
  obtain ⟨beforeInput, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨afterInput, afterGet, sizeEq⟩ := sizes.view beforeGet
  have inputBound : off + slow.have_.toNat ≤ afterInput.size := by omega
  obtain ⟨otherFinished, otherZ, otherS, zBefore, sBefore,
    otherSuffix, beforeJ, afterJ, suffixFields, suffixCursor⟩ :=
    final.writeback_passive_frame budget limit outputRange
      smallEntry lastPtr inputMargin (UInt32.toNat_lt slow.have_)
      afterGet inputBound
  have sameSuffix : finished = otherFinished := by
    have pair := Except.ok.inj (suffixRun.symm.trans otherSuffix)
    exact congrArg Prod.snd pair
  subst otherFinished
  have sameZ : zNext = otherZ := Option.some.inj
    (finalJ.good.live.hz.symm.trans afterJ.good.live.hz)
  have sameS : sNext = otherS := Option.some.inj
    (finalJ.good.live.hs.symm.trans afterJ.good.live.hs)
  subst otherZ; subst otherS
  exact ⟨(loopFields zBefore sBefore beforeJ).passive.trans suffixFields,
    suffixCursor⟩

theorem WordReady.loaded_passive_frame
    {c : Ctx} {ctx : FastLoopContext} {p : Parameters ctx}
    {h loopHeap finished loadedHeap : Heap} {q result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext loadedState : InflateState} {loaded slow : IL}
    (ready : WordReady p h q)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, loopHeap))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) loopHeap =
      .ok ((), finished))
    (smallEntry : q.bits.toNat < 8)
    (finishedJ : DefaultStateJ finished ctx.r ctx.zs zNext sNext)
    (environment : Env c finished ctx.r ctx.zs zNext sNext)
    (loadRun : runX (inflateAfterFast c) slow finished =
      .ok ((.ok (), loaded), loadedHeap))
    (loadedJ : DefaultStateJ loadedHeap ctx.r ctx.zs zNext loadedState) :
    FastPassiveFrame ctx.z zNext ctx.s loadedState := by
  have before := (ready.suffix_passive_frame loopRun suffixRun smallEntry finishedJ).1
  have after := inflateAfterFast_passive_fields environment loadRun loadedJ
  exact before.trans after

#print axioms WordReady.suffix_passive_frame
#print axioms WordReady.loaded_passive_frame
end Zlib.Inflate.Proofs.FastCommittedLoop
