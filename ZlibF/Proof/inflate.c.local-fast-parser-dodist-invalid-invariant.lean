import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dodist-invalid-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An invalid distance table entry in translated `dodist` consumes its
code bits, records the diagnostic and enters BAD without writing bytes. -/
theorem FastInputPacket.dodist_invalid_leaf_local_state
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false) :
    ∃ i after result slowNext,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      after = badHeap h r zs z s i ∧
      result.broke = true ∧ result.againD = false ∧
      result.in_ = l.in_ ∧ result.out = l.out ∧
      FastInputPacket after slowNext bs result ∧
      LocalStateJ after cutoff r zs
        { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
      DispatchBuffers after r slowNext bs ∧
      ByteViewSizes h after ∧
      stream slowNext bs = (stream slow bs).drop
        codes[index].bits.toNat := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers
    count countFits countSmall
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowNext bs afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  let selected : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 }
  have selectedPacket : FastInputPacket h slowNext bs selected :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  obtain ⟨i, after, badRun, heapEq, badPacket,
    badInvariant, badBuffers, sizes⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.badData_local_state selectedPacket) invariant codeBuffers
      streamPtr statePtr "invalid distance code" (by decide +kernel)
  let result : Zlib.Inffast.L := { selected with broke := true }
  have resultPacket : FastInputPacket after slowNext bs result :=
    ⟨badPacket.source, badPacket.cursor,
      badPacket.hold, badPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have notLinkEntry : (entry.op.toUInt32 &&& 64 == 0) = false := by
    simpa only [entry] using notLink
  have run : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notBaseEntry, notLinkEntry,
      Bool.false_eq_true, ite_false]
    rw [bind_ok (by simpa only [C.run] using badRun)]
    rfl
  refine ⟨i, after, result, slowNext, run, heapEq,
    rfl, rfl, rfl, rfl, resultPacket, badInvariant,
    badBuffers, sizes, ?_⟩
  simpa only [count, Zlib.Inffast.Proofs.toNat32]
    using dropped.2.2.1

end Zlib.Inflate.Local
