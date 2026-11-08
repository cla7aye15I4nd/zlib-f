import ZlibF.Proof.«inflate.c.fast-view-dolen-len-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-distance-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual length-extra and distance suffix changes only the original
output range when it continues without an error. -/
theorem FastInputPacket.dolenLen_normal_buffer_frame
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) ∧
      (result.broke = false →
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) := by
  obtain ⟨extra, used, consumed, slowNext, result, after,
    extraBound, usedBound, consumedBound, run, noAgain,
    packetAfter, buffersAfter, sizes, source, outcome,
    slowFrame⟩ :=
    packet.dolenLen_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask extraWidth bitsBound left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  refine ⟨result, after, run, ?_⟩
  intro notBroken
  obtain ⟨putEq, leftEq, _, _⟩ := slowFrame notBroken
  rcases outcome with post | ⟨i, broken, heapEq, _⟩
  · have frame := post.buffer_frame invariant.good.live.hz
      invariant.good.live.hs
    simpa only [putEq, leftEq] using frame
  · rw [notBroken] at broken
    cases broken

#print axioms FastInputPacket.dolenLen_normal_buffer_frame

end Zlib.Inflate.Proofs
