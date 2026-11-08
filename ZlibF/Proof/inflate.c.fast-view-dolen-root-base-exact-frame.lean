import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A one-pass base length loop changes only its final output prefix. -/
theorem FastInputPacket.dolen_root_base_loop_exact_frame
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
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after k,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
          .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  obtain ⟨result, after, k, run, out, lower, frame⟩ :=
    packet.dolen_base_leaf_exact_frame invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  obtain ⟨_, _, _, _, oldResult, oldAfter, _, _, _, oldRun,
      againL, _, _, _, _, _, _, _⟩ :=
    packet.dolen_base_leaf_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have same : oldResult = result ∧ oldAfter = after := by
    rw [run] at oldRun
    cases oldRun
    exact ⟨rfl, rfl⟩
  have againLExact : result.againL = false := by
    rw [← same.1]
    exact againL
  exact ⟨result, after, k, dolen_loop_one run againLExact,
    out, lower, frame⟩

#print axioms FastInputPacket.dolen_root_base_loop_exact_frame

end Zlib.Inflate.Proofs
