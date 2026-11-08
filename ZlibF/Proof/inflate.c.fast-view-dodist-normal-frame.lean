import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-distance-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Every continuing actual distance loop changes bytes only within its
entry output range. The BAD exit is treated separately by the bad-heap frame. -/
theorem FastInputPacket.dodist_loop_normal_buffer_frame
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      (result.broke = false →
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) := by
  obtain ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, run, noAgain, packetAfter,
    buffersAfter, sizes, source, outcome, slowFrame⟩ :=
    packet.dodist_loop_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr dcodePtr codesGet safe root held left avail length
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

#print axioms FastInputPacket.dodist_loop_normal_buffer_frame

end Zlib.Inflate.Proofs
