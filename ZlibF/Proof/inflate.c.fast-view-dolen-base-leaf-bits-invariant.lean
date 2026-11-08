import ZlibF.Proof.«inflate.c.fast-view-dolen-len-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A base length table entry consumes its code bits and then retains the
30-bit fast-loop bound through its length and distance suffix. -/
theorem FastInputPacket.dolen_base_leaf_bits_default_state
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
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      FastInputPacket after slowNext
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest))
        result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨_, used, _, slowNext, result, after,
    _, _, _, run, _, _, finalPacket, _, _, _, _, _⟩ :=
    packet.dolen_base_leaf_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth base
      extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  let entry : Code := lenCodes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeFits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
        using codeWidth
    omega
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: third :: fourth :: fifth :: rest) :=
    dropped.2.1
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have remaining : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    omega
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    len := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [baseLocal, entry] using extraWidth
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simp only [baseLocal, Zlib.Inffast.Proofs.toNat32]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨_, slowLen, result0, after0, lenRun,
    lenPacket, lenBound⟩ :=
    basePacket.dolenLen_bits_default_state invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound
      left avail baseLength outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span
      baseGuard
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at baseBool
      simp at baseBool
    simp [nonzero]
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run0 : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result0, after0) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result0, after0)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, baseBool,
      Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode,
      firstLocal, count, entry] using lenRun
  rw [run] at run0
  cases run0
  have sameBits : slowNext.bits = slowLen.bits :=
    finalPacket.bits.symm.trans lenPacket.bits
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    rw [sameBits]
    exact lenBound notBroken
  exact ⟨used, slowNext, result, after, run,
    finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
