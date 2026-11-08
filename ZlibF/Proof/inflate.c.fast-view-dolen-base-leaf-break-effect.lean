import ZlibF.Proof.«inflate.c.fast-view-dolen-len-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-length-class»
import ZlibF.Proof.«inffast.c.body»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A length-base leaf of the actual translated `dolen` enters the
checked extra-bit and distance suffix on caller byte views. -/
theorem FastInputPacket.dolen_base_leaf_break_effect
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
    ∃ extra used consumed slowNext result after,
      extra < 2 ^ (lenCodes[index].op &&& 15).toNat ∧
      used ≤ 5 ∧ consumed ≤ 48 ∧
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      FastInputPacket after slowNext
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest))
        result ∧
      DispatchBuffers after r slowNext
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowNext
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: fifth :: rest)) ∧
      (FastDistancePost h after r zs z s slowNext
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: rest))
        result dest output j (lenCodes[index].val.toNat + extra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i ∧
         DefaultStateJ after r zs
           { z with msg := .ref (.str i) 0 }
           { s with mode := BAD }) ∧
      (result.broke = false →
        slowNext.put = slow.put ∧
        slowNext.left = slow.left ∧
        slowNext.out_ = slow.out_ ∧
        slowNext.next = inputAdvance slow.next used) ∧
      ((result.broke = l.broke ∧
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
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
  have codeStream : stream slowCode
      (first :: second :: third :: fourth :: fifth :: rest) =
      List.drop entry.bits.toNat
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)) := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1
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
    simp only [baseLocal]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeSize : oo + slowCode.left.toNat ≤ output.size :=
    outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨extra, used, consumed, slowNext, result, after,
    extraBound, usedBound, consumedBound, lenRun,
    againD, finalPacket, finalBuffers, sizes, source,
    outcome, frameAfter, effect⟩ :=
    basePacket.dolenLen_break_effect invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound
      left avail baseLength baseOut codePut begPtr codeEnd
      outputGet outputWrite codeSize current beginLe span
      baseGuard
  have againL : result.againL = false := by
    have preserve := Zlib.Inffast.Proofs.dolenLen_againL
      (by simpa only [C.run] using lenRun)
    simpa only [baseLocal, afterCode, firstLocal] using preserve
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
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, baseBool,
      Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode,
      firstLocal, count, entry] using lenRun
  have totalBound : entry.bits.toNat + consumed ≤ 48 := by
    have entryWidth : entry.bits.toNat ≤ 15 := by
      simpa only [entry] using codeWidth
    omega
  refine ⟨extra, used, entry.bits.toNat + consumed,
    slowNext, result, after,
    by simpa only [baseLocal, entry,
      Zlib.Inffast.Proofs.mask15] using extraBound,
    usedBound, totalBound, run, againL, againD,
    finalPacket, finalBuffers, sizes, ?_, ?_, frameAfter,
    by simpa only [baseLocal, afterCode, firstLocal] using effect⟩
  · rw [codeStream] at source
    simpa only [List.drop_drop] using source
  · rcases outcome with post | bad
    · exact Or.inl (by simpa only [baseLocal,
        entry, UInt16.toNat_toUInt32] using post)
    · exact Or.inr bad

#print axioms FastInputPacket.dolen_base_leaf_break_effect

end Zlib.Inflate.Proofs
