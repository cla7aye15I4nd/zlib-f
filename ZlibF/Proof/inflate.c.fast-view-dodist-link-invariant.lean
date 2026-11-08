import ZlibF.Proof.«inflate.c.fast-view-dodist-invalid-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A second-level distance link retains the exact slow registers needed
to resume at its leaf. -/
theorem FastInputPacket.dodist_link_default_state_exact
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 }
    ∃ result slice,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, h) ∧
      slice < 2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      result.againD = true ∧ result.broke = l.broke ∧
      result.out = l.out ∧ result.len = l.len ∧
      FastInputPacket h slowNext bs result ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
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
  have opSmall : entry.op.toUInt32.toNat < 32 := by
    rw [Zlib.Inffast.Proofs.toNat32]
    simpa only [entry] using (show codes[index].op.toNat < 32 by omega)
  have firstAdd : C.run (Ptr.add c.dcode entry.val.toNat) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) := by
    rw [dcodePtr]
    have firstBound : baseOff + codes[index].val.toNat ≤
        codes.size :=
      Nat.le_trans (Nat.le_add_right _ _) subtable
    exact Ptr.add_nat_ok codesGet
      (by simpa only [entry] using firstBound)
  have shift : C.run (Zlib.Inffast.shl32 1 entry.op.toUInt32) h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  let slice : Nat := (selected.hold &&&
    ((((1 : UInt32) <<< entry.op.toUInt32) - 1).toUInt64)).toNat
  have sliceEq : slice = selected.hold.toNat %
      2 ^ entry.op.toNat := by
    have low := Zlib.Inffast.Proofs.hold_low64
      (x := selected.hold) (k := entry.op.toUInt32) opSmall
    simpa only [slice, Zlib.Inffast.Proofs.toNat32]
      using low
  have sliceBound : slice < 2 ^ entry.op.toNat := by
    rw [sliceEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have secondAdd : C.run (Ptr.add
      (.ref codeRef (baseOff + entry.val.toNat)) slice) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) := by
    exact Ptr.add_nat_ok codesGet (by
      have bound : baseOff + entry.val.toNat +
          2 ^ entry.op.toNat ≤ codes.size := by
        simpa only [entry] using subtable
      omega)
  let result : Zlib.Inffast.L := { selected with
    here := .ref codeRef (baseOff + entry.val.toNat + slice),
    againD := true }
  have resultPacket : FastInputPacket h slowNext bs result :=
    ⟨selectedPacket.source, selectedPacket.cursor,
      selectedPacket.hold, selectedPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have linkEntry : (entry.op.toUInt32 &&& 64 == 0) = true := by
    simpa only [entry] using link
  have run : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result, h) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result, h)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    change Ptr.add c.dcode entry.val.toNat h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) at firstAdd
    change Zlib.Inffast.shl32 1 entry.op.toUInt32 h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) at shift
    change Ptr.add (.ref codeRef (baseOff + entry.val.toNat)) slice h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) at secondAdd
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notBaseEntry, Bool.false_eq_true, ite_false,
      linkEntry, ite_true]
    rw [bind_ok load]
    rw [bind_ok firstAdd]
    rw [bind_ok shift]
    rw [bind_ok secondAdd]
    rfl
  refine ⟨result, slice, run,
    by simpa only [entry] using sliceBound,
    rfl, rfl, rfl, rfl, rfl, resultPacket,
    invariant, codeBuffers, ?_⟩
  simpa only [count, Zlib.Inffast.Proofs.toNat32]
    using dropped.2.2.1

/-- A second-level distance table entry follows a bounded link in the
actual `dodist` translation and retains the default caller-view packet. -/
theorem FastInputPacket.dodist_link_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    ∃ result slowNext slice,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, h) ∧
      slice < 2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      result.againD = true ∧ result.broke = l.broke ∧
      result.out = l.out ∧ result.len = l.len ∧
      FastInputPacket h slowNext bs result ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop
        codes[index].bits.toNat := by
  obtain ⟨result, slice, run, sliceBound, here,
    againD, broke, out, length, nextPacket, nextState,
    nextBuffers, source⟩ :=
    packet.dodist_link_default_state_exact invariant buffers
      herePtr dcodePtr codesGet codeIndex codeBits codeWidth
      notBase link linkWidth subtable
  exact ⟨result,
    { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 },
    slice, run, sliceBound, here, againD, broke, out, length,
    nextPacket, nextState, nextBuffers, source⟩

end Zlib.Inflate.Proofs
