import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-body-output-effect»
import ZlibF.Proof.«inflate.c.fast-view-break-effect-frame»
import ZlibF.Proof.«inflate.c.fast-memory-shape-source»
import ZlibF.Proof.«inflate.c.buffer-frame-compose»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast body writes only within the original caller output
interval. This includes all normal, BAD and TYPE exits. -/
theorem FastLoopReady.body_tight_frame
    {ctx : FastLoopContext} {h : Heap} {q result : Zlib.Inffast.L}
    {after : Heap}
    (ready : FastLoopReady ctx h q)
    (run : C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
      .ok (result, after)) :
    BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] ∧
    Shape h after ∧ Space.ro after ctx.dest = false := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
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
  obtain ⟨slowBreak, resultBreak, afterBreak, runBreak,
    breakEffect, _⟩ :=
    packet.fast_body_break_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have sameBreak : (resultBreak, afterBreak) = (result, after) :=
    Except.ok.inj (runBreak.symm.trans run)
  cases sameBreak
  have tight := fast_break_effect_buffer_frame breakEffect
    invariant.good.live.hz invariant.good.live.hs
  have exactFrame : BufferFrame h after
      (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] := by
    simpa only [putPtr, leftEq] using tight
  obtain ⟨slowEffect, resultEffect, afterEffect, runEffect,
    sourceEffect, _⟩ :=
    packet.fast_body_output_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have sameEffect : (resultEffect, afterEffect) = (result, after) :=
    Except.ok.inj (runEffect.symm.trans run)
  cases sameEffect
  have shape : Shape h after := sourceEffect.shape
    invariant.good.live.hz invariant.good.live.hs outputGet outputWrite
  have metadata := fastMemoryMetaFrameM_fast_body ctx.r ctx.c
    ctx.streamPtr q h result after run
  have ro : after.ro = h.ro := by
    simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq] at metadata
    exact metadata.1
  exact ⟨exactFrame, shape, by simpa only [Space.ro, ro] using outputWrite⟩

#print axioms FastLoopReady.body_tight_frame

end Zlib.Inflate.Proofs
