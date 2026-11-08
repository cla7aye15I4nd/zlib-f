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
    ∃ k, result.out = .ref ctx.dest k ∧ ctx.oo ≤ k ∧
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
  exact ⟨k, out, lower, by simpa only [putPtr] using frame, shape, ro⟩

#print axioms FastLoopReady.body_exact_frame

end Zlib.Inflate.Proofs
