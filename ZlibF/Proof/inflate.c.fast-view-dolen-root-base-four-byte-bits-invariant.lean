import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-four-byte-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-four-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A root base length entry leaves the one-pass translated `dolen` loop
with at most 30 held bits unless it breaks. -/
theorem FastInputPacket.dolen_root_base_loop_four_byte_bits_default_state
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
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
    (held : 16 ≤ slow.bits.toNat)
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
    ∃ used slowNext result after,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun q => pure (q.againL, q)) l) h =
          .ok (result, after) ∧
      FastInputPacket after slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨_, used, _, slowNext, result, after,
    _, _, _, run, _, _, finalPacket, _, _, _, _, _⟩ :=
    packet.dolen_root_base_loop_four_byte_frame_default_state
      invariant buffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq herePtr lenGet indexBound codeFits
      codeWidth base extraWidth lengthBase dcodePtr distGet
      distSafe distMask bitsBound held left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  have codeHeld : 1 + lenCodes[index].bits.toNat ≤ slow.bits.toNat := by
    omega
  obtain ⟨_, slowLeaf, result0, after0, leafRun,
    leafPacket, leafBound⟩ :=
    packet.dolen_base_leaf_four_byte_bits_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth codeHeld base
      extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  obtain ⟨_, _, _, _, _, _, _, _, _, leafRun1,
    noAgain, _, _, _, _, _, _, _⟩ :=
    packet.dolen_base_leaf_four_byte_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth codeHeld base
      extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  rw [leafRun] at leafRun1
  cases leafRun1
  have loopRun := dolen_loop_one leafRun noAgain
  rw [run] at loopRun
  cases loopRun
  have sameBits : slowNext.bits = slowLeaf.bits :=
    finalPacket.bits.symm.trans leafPacket.bits
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    rw [sameBits]
    exact leafBound notBroken
  exact ⟨used, slowNext, result, after,
    run, finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
