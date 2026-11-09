import ZlibF.Proof.«inflate.c.local-fast-loop-metadata»
import ZlibF.Proof.«inflate.c.local-fast-parser-body-complete-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-effects-body»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated body itself supplies every local loop observation.
Its representation and effect producers are tied to this same execution. -/
theorem FastLoopReady.observe
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady cutoff ctx h q) :
    ∃ result after, FastLoopBodyObserved cutoff ctx h q result after := by
  rcases ready with ⟨slow, bs, output, off, start, packet,
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
  obtain ⟨used, consumed, witness, result, after, zNext, sNext, _, _, run,
    returnedPacket, nextJ, _, sizes, _⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.fast_body_local_state packet)
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask ctx.dcodePtr
      distGet ctx.distSafe ctx.distMask bitsBound left avail outPtr putPtr ctx.begPtr
      endPtr outputGet outputWrite outputSize current beginLe span guard
  have effect := (Zlib.Inflate.Local.FastInputPacket.fast_body_effect packet)
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask ctx.dcodePtr
      distGet ctx.distSafe ctx.distMask bitsBound left avail outPtr putPtr ctx.begPtr
      endPtr outputGet outputWrite outputSize current beginLe span guard run
  exact ⟨result, after, .intro slow _ output off start packet invariant buffers codesGet distGet
    bitsBound leftEq outEq putPtr nextPtr lastPtr inputMargin outPtr outputGet outputWrite
    outputSize current beginLe span guard zNext sNext witness _ run nextJ returnedPacket sizes effect⟩

/-- One actual translated body and condition preserve the local loop
relation or exit. Continuing iterations strictly decrease output space. -/
theorem FastLoopReady.step
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady cutoff ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧
          FastLoopExit cutoff ctx after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
          FastLoopReady cutoff ctx after result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  obtain ⟨result, after, observed⟩ := ready.observe
  exact ⟨result, after, FastLoopReady.step_of_observed observed⟩

end Zlib.Inflate.Local
