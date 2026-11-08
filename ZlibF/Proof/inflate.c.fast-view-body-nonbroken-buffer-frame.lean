import ZlibF.Proof.«inflate.c.fast-view-body-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A continuing actual fast body writes only in the output interval from
its entry. This includes the case where input and output share a byte object. -/
theorem FastInputPacket.fast_body_nonbroken_buffer_frame
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
      (result.broke = false →
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) := by
  obtain ⟨slowFinal, result, after, run, effect, frame⟩ :=
    packet.fast_body_output_effect invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  refine ⟨result, after, run, fun notBroken => ?_⟩
  obtain ⟨putEq, leftEq⟩ := frame notBroken
  rw [← putEq, ← leftEq]
  exact effect.buffer_frame invariant.good.live.hz
    invariant.good.live.hs

#print axioms FastInputPacket.fast_body_nonbroken_buffer_frame

end Zlib.Inflate.Proofs
