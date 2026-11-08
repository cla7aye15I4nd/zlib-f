import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-length-four-byte-budget»
import ZlibF.Proof.«inffast.c.dolen-base-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- An actual selected length-base call charges both its input cursor and
held bits to the same byte count, including a broken distance suffix. -/
theorem FastInputPacket.dolen_base_leaf_four_byte_bit_budget
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
    (held : 1 + lenCodes[index].bits.toNat ≤ slow.bits.toNat)
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
    ∃ result after pulled,
      pulled ≤ 4 ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨extra, usedGhost, consumed, slowNext, result, after,
    _, _, _, run, _⟩ :=
    packet.dolen_base_leaf_four_byte_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth held base
      extraWidth lengthBase dcodePtr distGet distSafe distMask
      bitsBound left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  let entry : Code := lenCodes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeFits
  have countSmall : count.toNat < 64 := by
    have cast : count.toNat = lenCodes[index].bits.toNat := rfl
    omega
  let firstLocal : Zlib.Inffast.L := { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state buffers count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: rest) afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: third :: fourth :: rest) := dropped.2.1
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have remaining : slowCode.bits.toNat = slow.bits.toNat - count.toNat := dropped.2.2.2
    omega
  have codeHeld : 1 ≤ slowCode.bits.toNat := by
    have remaining : slowCode.bits.toNat = slow.bits.toNat - count.toNat := dropped.2.2.2
    have cast : count.toNat = lenCodes[index].bits.toNat := rfl
    omega
  let baseLocal := Zlib.Inffast.Proofs.lengthBaseLocal l entry
  have basePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor, codePacket.hold, codePacket.bits⟩
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    change (entry.op.toUInt32 &&& 15).toNat ≤ 5
    rw [Zlib.Inffast.Proofs.mask15]
    exact extraWidth
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simp only [baseLocal, Zlib.Inffast.Proofs.lengthBaseLocal]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have suffixRun : C.run (Zlib.Inffast.Proofs.dolenLen c baseLocal) h =
      .ok (result, after) :=
    Zlib.Inffast.Proofs.dolen_base_suffix_run load codeWidth baseBool run
  obtain ⟨pulled, bound, cursor, bits⟩ :=
    basePacket.dolenLen_four_byte_result_bit_budget invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound codeHeld
      left avail baseLength outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard suffixRun
  have available : entry.bits.toNat ≤ l.bits.toNat := by
    rw [packet.bits]
    exact codeFits
  have codeLedger := Zlib.Inffast.Proofs.lengthBaseLocal_bit_ledger l entry available
  refine ⟨result, after, pulled, bound, run, ?_, ?_⟩
  · simpa only [baseLocal, Zlib.Inffast.Proofs.lengthBaseLocal] using cursor
  · change result.bits.toNat ≤ (Zlib.Inffast.Proofs.lengthBaseLocal l entry).bits.toNat +
      8 * pulled at bits
    omega

#print axioms FastInputPacket.dolen_base_leaf_four_byte_bit_budget
end Zlib.Inflate.Proofs
