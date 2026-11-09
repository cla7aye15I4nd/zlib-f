import ZlibF.Proof.«inflate.c.local-fast-exact-output-parser-body»
import ZlibF.Proof.«inflate.c.local-fast-loop-summary»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Each actual loop body writes only up to its returned output cursor. -/
theorem FastLoopReady.body_exact_output
    {cutoff : Nat} {ctx : FastLoopContext} {h after : Heap} {q result : Zlib.Inffast.L}
    (ready : FastLoopReady cutoff ctx h q)
    (run : C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after)) :
    ∃ j k, q.out = .ref ctx.dest j ∧ result.out = .ref ctx.dest k ∧
      ctx.oo ≤ j ∧ j ≤ k ∧ k ≤ ctx.oo + ctx.leftTotal.toNat ∧
      BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
        [⟨.ref ctx.dest ctx.oo, k - ctx.oo⟩] := by
  rcases ready with ⟨slow, bs, output, off, j, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ := packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  obtain ⟨finish, pointer, lower, frame⟩ :=
    Zlib.Inflate.Local.FastInputPacket.fast_body_exact_output packet
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask ctx.dcodePtr
      distGet ctx.distSafe ctx.distMask bitsBound left avail outPtr putPtr ctx.begPtr
      endPtr outputGet outputWrite outputSize current beginLe span guard run
  have effect := Zlib.Inflate.Local.FastInputPacket.fast_body_effect packet
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask ctx.dcodePtr
      distGet ctx.distSafe ctx.distMask bitsBound left avail outPtr putPtr ctx.begPtr
      endPtr outputGet outputWrite outputSize current beginLe span guard run
  obtain ⟨bounded, boundedPtr, _, upper⟩ := effect.output
  have same : bounded = finish := (Ptr.ref.inj (boundedPtr.symm.trans pointer)).2
  subst bounded
  have room := fast_output_max_room_of_guard outPtr endPtr outputGet outputSize current avail guard
  refine ⟨j, finish, outPtr, pointer, current, lower, ?_, ?_⟩
  · rw [← leftEq]
    omega
  · exact BufferFrame.singleton_widen frame current (by omega)

end Zlib.Inflate.Local
