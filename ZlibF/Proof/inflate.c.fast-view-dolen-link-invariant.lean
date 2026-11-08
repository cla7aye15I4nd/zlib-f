import ZlibF.Proof.«inflate.c.fast-view-dolen-literal-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A second-level length link retains the exact slow registers needed
to resume at its leaf. -/
theorem FastInputPacket.dolen_link_default_state_exact
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code} {index baseOff : Nat}
    (herePtr : l.here = .ref codeRef index)
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (link : (codes[index].op.toUInt32 &&& 64 == 0) = true)
    (linkWidth : codes[index].op.toNat ≤ 15)
    (subtable : baseOff + codes[index].val.toNat +
      2 ^ codes[index].op.toNat ≤ codes.size) :
    let slowNext : IL := { slow with
      hold := slow.hold >>> codes[index].bits.toUInt32.toUInt64,
      bits := slow.bits - codes[index].bits.toUInt32 }
    ∃ result slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, h) ∧
      slice < 2 ^ codes[index].op.toNat ∧
      result.here = .ref codeRef
        (baseOff + codes[index].val.toNat + slice) ∧
      result.againL = true ∧ result.broke = l.broke ∧
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
    { l with againL := false, op := count }
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
  have firstAdd : C.run (Ptr.add c.lcode entry.val.toNat) h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) := by
    rw [lcodePtr]
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
    againL := true }
  have resultPacket : FastInputPacket h slowNext bs result :=
    ⟨selectedPacket.source, selectedPacket.cursor,
      selectedPacket.hold, selectedPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzeroEntry : entry.op.toUInt32 ≠ 0 := by
      intro zero
      have zero8 : entry.op = 0 := by
        have natZero : entry.op.toNat = 0 := by
          simpa only [UInt8.toNat_toUInt32, UInt32.toNat_zero]
            using congrArg UInt32.toNat zero
        exact UInt8.toNat_inj.mp (by simpa using natZero)
      exact nonzero (by simpa only [entry] using zero8)
    simp [nonzeroEntry]
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have linkEntry : (entry.op.toUInt32 &&& 64 == 0) = true := by
    simpa only [entry] using link
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, h) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, h)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    change Ptr.add c.lcode entry.val.toNat h =
      .ok (.ref codeRef (baseOff + entry.val.toNat), h) at firstAdd
    change Zlib.Inffast.shl32 1 entry.op.toUInt32 h =
      .ok ((1 : UInt32) <<< entry.op.toUInt32, h) at shift
    change Ptr.add (.ref codeRef (baseOff + entry.val.toNat)) slice h =
      .ok (.ref codeRef (baseOff + entry.val.toNat + slice), h) at secondAdd
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, notBaseEntry, Bool.false_eq_true, ite_false,
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

/-- A safe length-table root link reaches one bounded leaf of the actual
`dolen` translation and keeps the caller state ready for the next pass. -/
theorem FastInputPacket.dolen_root_link_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      LenLeaf rootEntry.bits.toNat
        (codes.getD (baseOff + rootEntry.val.toNat + slice)
          default) ∧
      (codes.getD (baseOff + rootEntry.val.toNat + slice)
          default).bits.toNat ≤ slowNext.bits.toNat ∧
      FastInputPacket h slowNext bs linked ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext bs ∧
      stream slowNext bs = (stream slow bs).drop
        rootEntry.bits.toNat := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, here,
    againL, _, _, _, linkedPacket, _, linkedBuffers,
    source⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  let slowNext : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := len_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq] using target.2.1
  have targetBits : codes[targetIndex].bits.toNat ≤
      slowNext.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowNext] using source)
  refine ⟨linked, slice, slowNext, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using here,
    by simpa only [rootEq, targetIndex, targetEq]
      using targetLeaf,
    by simpa only [rootEq, targetIndex, targetEq]
      using targetBits,
    linkedPacket, invariant, linkedBuffers, ?_⟩
  simpa only [rootEq] using source

/-- The same selected root link leaves the fast output cursor, match
length and break flag unchanged. -/
theorem FastInputPacket.dolen_root_link_registers
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    {linked : Zlib.Inffast.L}
    (run : C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h)) :
    linked.out = l.out ∧ linked.len = l.len ∧
      linked.broke = l.broke := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨width, _, opWidth, subtable, _⟩
  have fits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨actual, _, actualRun, _, _, _, broke,
    out, len, _, _, _, _⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound fits width
      rootLink.1 notBase linkBool opWidth subtable
  rw [run] at actualRun
  cases actualRun
  exact ⟨out, len, broke⟩

end Zlib.Inflate.Proofs
