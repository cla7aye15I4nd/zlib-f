import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual root length-base source branch retains its output or
diagnostic heap effect through length-extra and distance decoding. -/
theorem FastInputPacket.dolen_root_base_output_effect
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
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
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
    ∃ slowNext result after,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      FastOutputEffect h after r zs z s slowNext dest ∧
      (result.broke = false →
        slowNext.put = slow.put ∧ slowNext.left = slow.left) := by
  obtain ⟨extra, used, consumed, slowNext, result, after,
    extraBound, usedBound, consumedBound, run, noAgain,
    noAgainD, packetAfter, buffersAfter, sizes, source,
    outcome, slowFrame⟩ :=
    packet.dolen_root_base_loop_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth base extraWidth
      lengthBase dcodePtr distGet distSafe distMask bitsBound held
      left avail outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  exact ⟨slowNext, result, after, run,
    distance_outcome_output_effect outcome,
    fun notBroken => ⟨(slowFrame notBroken).1,
      (slowFrame notBroken).2.1⟩⟩

#print axioms FastInputPacket.dolen_root_base_output_effect

end Zlib.Inflate.Proofs
