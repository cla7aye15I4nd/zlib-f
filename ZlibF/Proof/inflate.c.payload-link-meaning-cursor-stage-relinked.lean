import ZlibF.Proof.«inflate.c.payload-two-root-decoded-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeShort
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.payload_length_link_second_read
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    (entry : Code) {slice : Nat}
    (width : entry.bits.toNat ≤ 15)
    (fits : entry.bits.toNat + entry.op.toNat ≤ slow.bits.toNat)
    (sliceEq : slice =
      (l.hold >>> entry.bits.toUInt32.toUInt64).toNat %
        2 ^ entry.op.toNat) :
    readBits entry.op.toNat
      ((stream slow bs).drop entry.bits.toNat) =
      some (slice,
        (stream slow bs).drop
          (entry.bits.toNat + entry.op.toNat)) := by
  have firstFits : entry.bits.toNat ≤ slow.bits.toNat := by omega
  have shift :
      (l.hold >>> entry.bits.toUInt32.toUInt64).toNat =
      slow.hold.toNat / 2 ^ entry.bits.toNat := by
    rw [packet.hold]
    simpa only [toNat32] using
      (u64_shr (x := slow.hold) (n := entry.bits.toUInt32)
        (by simpa only [toNat32] using
          (show entry.bits.toNat < 64 by omega)))
  have dropEq : (stream slow bs).drop entry.bits.toNat =
      bitsOfNat (slow.hold.toNat / 2 ^ entry.bits.toNat)
        (slow.bits.toNat - entry.bits.toNat) ++ bytesBits bs := by
    rw [stream, List.drop_append_of_le_length
      (by simpa only [natBits_length] using firstFits)]
    rw [natBits_drop _ _ _ firstFits]
    rw [natBits_testBit]
    rfl
  have read := readBits_bitsOfNat entry.op.toNat
    (slow.bits.toNat - entry.bits.toNat)
    (slow.hold.toNat / 2 ^ entry.bits.toNat)
    (bytesBits bs) (by omega)
  rw [← dropEq] at read
  have restEq : bitsOfNat
      ((slow.hold.toNat / 2 ^ entry.bits.toNat) /
        2 ^ entry.op.toNat)
      (slow.bits.toNat - entry.bits.toNat - entry.op.toNat) ++
      bytesBits bs =
      (stream slow bs).drop
        (entry.bits.toNat + entry.op.toNat) := by
    rw [← List.drop_drop, dropEq]
    rw [List.drop_append_of_le_length
      (by simp only [bitsOfNat_length]; omega)]
    rw [bitsOfNat_drop]
    omega
  rw [restEq] at read
  simpa only [sliceEq, shift] using read


theorem FastInputPacket.payload_dolen_root_link_default_state_with_slice
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
      slice = (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat ∧
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
  rw [rootEq, ite_eq_left rootLink] at selected
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
  obtain ⟨linked, slice, firstRun, sliceBound, sliceEq, here,
    againL, _, _, _, linkedPacket, _, linkedBuffers,
    source⟩ :=
    packet.payload_dolen_link_default_state_exact_with_slice invariant buffers
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
    by simpa only [rootEq] using sliceEq,
    by simpa only [rootEq, targetIndex] using here,
    by simpa only [rootEq, targetIndex, targetEq]
      using targetLeaf,
    by simpa only [rootEq, targetIndex, targetEq]
      using targetBits,
    linkedPacket, invariant, linkedBuffers, ?_⟩
  simpa only [rootEq] using source


theorem FastInputPacket.payload_length_selected_link_match_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice used : Nat} {lens : List Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (root : rootSlice < 2 ^ rootWidth)
    (rootIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (queryLink : IsLink LENS
      (codes.getD (baseOff + rootSlice) default) = true)
    (held : 15 ≤ slow.bits.toNat)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, rest))
    (lengthMax : symbol ≤ 285) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      FastInputPacket h slowNext bs linked ∧
      stream slowNext bs = (stream slow bs).drop rootEntry.bits.toNat ∧
      slice = (l.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat ∧
      SymbolEntry LENS symbol
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default) ∧
      rest = (stream slow bs).drop
        (rootEntry.bits.toNat +
          (codes.getD (baseOff + rootEntry.val.toNat + slice) default).bits.toNat) := by
  let rootEntry := codes.getD (baseOff + rootSlice) default
  obtain ⟨linked, slice, slowNext, firstRun, againL,
    sliceBound, sliceEq, linkedHere, targetLeaf, _,
    linkedPacket, _, _, sourceDrop⟩ :=
    packet.payload_dolen_root_link_default_state_with_slice
      invariant buffers herePtr lcodePtr codesGet safe
      root link held
  let target := codes.getD
    (baseOff + rootEntry.val.toNat + slice) default
  have rootRead : readBits rootWidth (stream slow bs) =
      some (rootSlice, (stream slow bs).drop rootWidth) := by
    have rootFits : rootWidth ≤ slow.bits.toNat := by
      have width := meaning.rootTable.2.1
      omega
    have read := readBits_held_stream slow bs rootWidth rootFits
    simpa only [← packet.hold, ← rootIndex] using read
  have rootBound : baseOff + rootSlice < codes.size := by
    have rootSize := safe.2.1
    omega
  have rootCell : codes[baseOff + rootSlice]? = some rootEntry := by
    simp [rootEntry, Array.getD_eq_getD_getElem?, rootBound]
  have selected := safe.2.2 rootSlice root
  have rootEq : rootEntry = codes[baseOff + rootSlice] := by
    simp [rootEntry, Array.getD_eq_getD_getElem?, rootBound]
  have rootGet : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootGet] using link
  rw [rootGet, ite_eq_left rootLink] at selected
  obtain ⟨rootWidthBound, _, opWidth, _, _⟩ := selected
  obtain ⟨rootBits, subSafe⟩ :=
    meaning.subtables rootSlice rootEntry root rootCell queryLink
  have subBits : rootEntry.bits.toNat + rootEntry.op.toNat ≤ 15 :=
    subSafe.2.2.1
  have linkFits : rootEntry.bits.toNat + rootEntry.op.toNat ≤
      slow.bits.toNat := by
    omega
  have linkWidth : rootEntry.bits.toNat ≤ 15 := by
    omega
  have secondRead := packet.payload_length_link_second_read
    rootEntry linkWidth linkFits sliceEq
  have targetBound : baseOff + rootEntry.val.toNat + slice <
      codes.size := (len_table_link_target safe root link sliceBound).1
  have targetCell : codes[baseOff + rootEntry.val.toNat + slice]? =
      some target := by
    simp [target, Array.getD_eq_getD_getElem?, targetBound]
  have queryLinkCode :
      (rootEntry.op != 0 && (rootEntry.op &&& 0xf0) == 0) = true := by
    simpa [IsLink, rootEntry] using queryLink
  have query : tableRead LENS codes baseOff rootWidth
      (stream slow bs) =
      some (target, rootEntry.bits.toNat + target.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, rootCell]
    simp only [queryLinkCode, ite_true, secondRead,
      targetCell]
    rfl
  have consumed : rootEntry.bits.toNat + target.bits.toNat ≤
      (stream slow bs).length := by
    have codeLe : rootEntry.bits.toNat + target.bits.toNat ≤ 15 := by
      have raw : target.bits.toNat + rootEntry.bits.toNat ≤ 15 := targetLeaf.1
      omega
    simp only [stream, List.length_append, natBits_length]
    omega
  have padding : padded (stream slow bs) = stream slow bs := by
    have long : 15 ≤ (stream slow bs).length := by
      simp only [stream, List.length_append, natBits_length]
      omega
    simp [padded, Nat.sub_eq_zero_of_le long]
  have long : 15 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length]
    omega
  obtain ⟨other, otherCount, otherQuery, classification⟩ :=
    meaning.classify (stream slow bs) long
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using lengthMax
  have acceptedOther : LeafAccepted LENS other :=
    classification.mpr ⟨symbol, rest, decoded, valid⟩
  have same : (other, otherCount) =
      (target, rootEntry.bits.toNat + target.bits.toNat) :=
    Option.some.inj (otherQuery.symm.trans query)
  have accepted : LeafAccepted LENS target := by
    simpa only [(Prod.mk.inj same).1] using acceptedOther
  obtain ⟨found, _, foundMeaning, _, foundDecode, _⟩ :=
    meaning.short (stream slow bs) target
      (rootEntry.bits.toNat + target.bits.toNat)
      (by rw [padding]; exact query) consumed accepted
  have decodedEq := Option.some.inj (foundDecode.symm.trans decoded)
  have symbolEq : found = symbol := congrArg Prod.fst decodedEq
  have restEq : rest = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) :=
    (congrArg Prod.snd decodedEq).symm
  subst found
  exact ⟨linked, slice, slowNext, firstRun, againL,
    linkedHere, linkedPacket, sourceDrop, sliceEq, foundMeaning, restEq⟩


end Zlib.Inflate.Proofs
