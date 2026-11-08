import ZlibF.Proof.«inflate.c.fast-view-body-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-loop-body-tight-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual body run gives the returned output cursor and its exact frame. -/
theorem FastLoopReady.body_exact_frame
    {ctx : FastLoopContext} {h : Heap} {q result : Zlib.Inffast.L}
    {after : Heap}
    (ready : FastLoopReady ctx h q)
    (run : C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
      .ok (result, after)) :
    ∃ j k, q.out = .ref ctx.dest j ∧
      result.out = .ref ctx.dest k ∧
      ctx.oo ≤ j ∧ j ≤ k ∧
      k ≤ ctx.oo + ctx.leftTotal.toNat ∧
      BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] ∧
      Shape h after ∧ Space.ro after ctx.dest = false := by
  have ⟨_, shape, ro⟩ := ready.body_tight_frame run
  rcases ready with ⟨slow, bs, output, off, j, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth,
    rest, rfl⟩ := packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  obtain ⟨produced, finalHeap, k, actualRun, out, lower, frame⟩ :=
    packet.fast_body_exact_frame invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have same : (produced, finalHeap) = (result, after) :=
    Except.ok.inj (actualRun.symm.trans run)
  cases same
  obtain ⟨bounded, boundedHeap, boundedArray, boundedK,
    boundedRun, boundedOut, monotone, upper, _, _⟩ :=
    packet.fast_body_output_bound invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have sameBound : (bounded, boundedHeap) = (result, after) :=
    Except.ok.inj (boundedRun.symm.trans run)
  cases sameBound
  have kEq : boundedK = k := by
    exact (Ptr.ref.inj (boundedOut.symm.trans out)).2
  subst boundedK
  refine ⟨j, k, outPtr, out, current, monotone, ?_, ?_, shape, ro⟩
  · simpa only [leftEq] using upper
  · simpa only [putPtr] using frame

#print axioms FastLoopReady.body_exact_frame

end Zlib.Inflate.Proofs
