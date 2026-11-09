import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-one-byte»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-leaf-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-leaf-one-byte-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dodist_base_leaf_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
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
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    (extraBound : (codes[index].op.toUInt32 &&& 15).toNat ≤ 13)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (Zlib.Inffast.dodist c l) h = .ok (value, finalHeap)) :
    FastExecEffect h finalHeap r zs z s slow dest j l value 2 258 := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: rest) firstLocal :=
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
      (first :: second :: rest) afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: rest) := dropped.2.1
  have codeStream : stream slowCode (first :: second :: rest) =
      (stream slow (first :: second :: rest)).drop
        entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeLeft : slowCode.left ≠ 0 := left
  have codeAvail : 258 ≤ slowCode.left.toNat := avail
  have codeSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  have baseExtra : baseLocal.op.toNat ≤ 13 := extraBound
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat ≤ 258 := length
  have baseEntry : (entry.op.toUInt32 &&& 16 != 0) = true := by
    simpa only [entry] using base
  obtain ⟨used, slowNext, result, after, usedBound,
    baseRun, post, afterStream⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dodistBase_local_state basePacket) invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard
  have effect :=
    Zlib.Inflate.Local.FastInputPacket.dodistBase_effect basePacket invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard baseRun
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
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
    simp only [baseEntry, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode, firstLocal,
      count, entry] using baseRun
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rcases same with ⟨rfl, rfl⟩
  have bitLe : baseLocal.bits.toNat ≤ l.bits.toNat := by
    change (l.bits - count).toNat ≤ l.bits.toNat
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [packet.bits]; exact countFits)]
    omega
  exact effect.prefix (pulled := 0) rfl rfl rfl
    (by simp only [baseLocal, afterCode, firstLocal, inputAdvance_zero])
    (by omega) (Nat.le_trans bitLe (Nat.le_max_left _ _)) (by omega) (by omega)

#print axioms FastInputPacket.dodist_base_leaf_effect

theorem FastInputPacket.dodist_base_leaf_one_byte_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (Zlib.Inffast.dodist c l) h = .ok (value, finalHeap)) :
    FastExecEffect h finalHeap r zs z s slow dest j l value 1 258 := by
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
  have codeHeld : 5 ≤ slowCode.bits.toNat := by
    have bitsAfter : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    have codeSmall : count.toNat = codes[index].bits.toNat := by
      rfl
    omega
  have codeStream : stream slowCode (first :: rest) =
      (stream slow (first :: rest)).drop
        entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeLeft : slowCode.left ≠ 0 := left
  have codeAvail : 258 ≤ slowCode.left.toNat := avail
  have codeSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  have baseExtra : baseLocal.op.toNat ≤ 13 := extraBound
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat ≤ 258 := length
  have baseEntry : (entry.op.toUInt32 &&& 16 != 0) = true := by
    simpa only [entry] using base
  obtain ⟨used, slowNext, result, after, usedBound,
    baseRun, post, afterStream⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dodistBase_one_byte_local_state basePacket) invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      codeHeld baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard
  have effect :=
    Zlib.Inflate.Local.FastInputPacket.dodistBase_one_byte_effect basePacket invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      codeHeld baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard baseRun
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
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
    simp only [baseEntry, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode, firstLocal,
      count, entry] using baseRun
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rcases same with ⟨rfl, rfl⟩
  have bitLe : baseLocal.bits.toNat ≤ l.bits.toNat := by
    change (l.bits - count).toNat ≤ l.bits.toNat
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [packet.bits]; exact countFits)]
    omega
  exact effect.prefix (pulled := 0) rfl rfl rfl
    (by simp only [baseLocal, afterCode, firstLocal, inputAdvance_zero])
    (by omega) (Nat.le_trans bitLe (Nat.le_max_left _ _)) (by omega) (by omega)

#print axioms FastInputPacket.dodist_base_leaf_one_byte_effect

end Zlib.Inflate.Local
