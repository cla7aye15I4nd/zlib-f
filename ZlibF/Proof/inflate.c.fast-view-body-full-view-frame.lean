import ZlibF.Proof.«inflate.c.fast-view-body-output-effect»
import ZlibF.Proof.«inflate.c.fast-view-full-view-frame»
import ZlibF.Proof.«inflate.c.fast-view-body-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The entire actual fast body changes only its stream/state roots and the
whole writable output view. The narrower caller interval remains the next
source-effect transport obligation. -/
theorem FastInputPacket.fast_body_full_view_buffer_frame
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨.ref dest 0, output.size⟩] := by
  obtain ⟨slowEffect, resultEffect, afterEffect,
    effectRun, effect, _⟩ :=
    packet.fast_body_output_effect invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  obtain ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, bodyRun,
    finalPacket, finalJ, finalBuffers, sizes, source,
    slowFrame⟩ :=
    packet.fast_body_frame_default_state invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  have same : resultEffect = result ∧ afterEffect = after := by
    have eq := effectRun
    rw [bodyRun] at eq
    cases eq
    exact ⟨rfl, rfl⟩
  have sizesEffect : ByteViewSizes h afterEffect := by
    rw [same.2]
    exact sizes
  exact ⟨resultEffect, afterEffect, effectRun,
    effect.full_view_buffer_frame sizesEffect outputGet outputWrite
      invariant.good.live.hz invariant.good.live.hs⟩

#print axioms FastInputPacket.fast_body_full_view_buffer_frame

end Zlib.Inflate.Proofs
