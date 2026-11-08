import ZlibF.Proof.«inflate.c.fast-view-dodist-base-one-byte-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-one-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A base distance table entry first removes its code bits, then runs the
guarded distance-extra-bit suffix; the resulting held count stays bounded. -/
theorem FastInputPacket.dodist_base_leaf_one_byte_bits_default_state
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (held : 5 + codes[index].bits.toNat ≤ slow.bits.toNat)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    (extraBound : (codes[index].op.toUInt32 &&& 15).toNat ≤ 13)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
      used ≤ 1 ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      FastDistancePost h after r zs z s slowNext
        ((first :: rest).drop used) result
        dest output j l.len.toNat ∧
      stream slowNext ((first :: rest).drop used) =
        ((stream slow (first :: rest)).drop
          codes[index].bits.toNat).drop
            (codes[index].op.toUInt32 &&& 15).toNat ∧
      slowNext.put = slow.put ∧
      slowNext.left = slow.left ∧
      slowNext.out_ = slow.out_ ∧
      slowNext.next = inputAdvance slow.next used ∧
      slowNext.bits.toNat ≤ 30 := by
  obtain ⟨used, slowNext, result, after, usedLimit, run,
    post, source, putEq, leftEq, outEq, nextEq⟩ :=
    packet.dodist_base_leaf_one_byte_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr codesGet codeIndex codeBits codeWidth held base
      extraBound left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: rest) firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers
    count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: rest) afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: rest) := dropped.2.1
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have countEq := dropped.2.2.2
    change (slow.bits - count).toNat =
      slow.bits.toNat - count.toNat at countEq
    change (slow.bits - count).toNat ≤ 30
    omega
  have codeHeld : 5 ≤ slowCode.bits.toNat := by
    have countEq := dropped.2.2.2
    change (slow.bits - count).toNat =
      slow.bits.toNat - count.toNat at countEq
    have countNat : count.toNat = codes[index].bits.toNat := rfl
    change 5 ≤ (slow.bits - count).toNat
    omega
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨used0, slowBase, result0, after0, _, baseRun,
    basePost, _, bound0⟩ :=
    basePacket.dodistBase_one_byte_bits_default_state invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      codeHeld extraBound codeBound left avail length outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current
      beginLe span baseGuard
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have baseEntry : (entry.op.toUInt32 &&& 16 != 0) = true := by
    simpa only [entry] using base
  have run0 : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result0, after0) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result0, after0)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [baseEntry, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode, firstLocal,
      count, entry] using baseRun
  rw [run] at run0
  cases run0
  have sameBits : slowNext.bits = slowBase.bits :=
    post.1.bits.symm.trans basePost.1.bits
  have finalBound : slowNext.bits.toNat ≤ 30 := by
    rw [sameBits]
    exact bound0
  exact ⟨used, slowNext, result, after, usedLimit, run,
    post, source, putEq, leftEq, outEq, nextEq, finalBound⟩

end Zlib.Inflate.Proofs
