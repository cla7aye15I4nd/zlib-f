import ZlibF.Proof.«inflate.c.fast-semantic-slice-05»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual translated length-extra suffix, including zero, no-refill,
and one-pull branches, retains the exact independent length extra value. -/
theorem FastInputPacket.dolenLen_length_extra_semantics
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
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
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
    {symbol lengthExtra : Nat} {r1 r2 : List Bool}
    (width : l.op.toNat =
      lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2)) :
    ∃ used consumed slowNext result after,
      used ≤ 5 ∧ consumed ≤ 33 ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result dest output j (l.len.toNat + lengthExtra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  by_cases zero : l.op = 0
  · have extraZero : lengthExtra = 0 := by
      rw [← width, zero] at lengthBits
      have pair := Option.some.inj lengthBits
      simpa only [readBits, Prod.fst] using
        (congrArg Prod.fst pair).symm
    have length0 : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [zero] at length
      simp only [UInt32.toNat_zero] at length
      simp at length
      omega
    obtain ⟨used, consumed, slowNext, result, after,
      usedBound, consumedBound, run, packetNext,
      sourceNext, outcome⟩ :=
      packet.dolenLen_zero_extra_semantics invariant
        buffers zero streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq dcodePtr codesGet safe mask
        bitsBound left avail length0 outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    refine ⟨used, consumed, slowNext, result, after,
      by omega, by omega, run, packetNext, sourceNext, ?_⟩
    simpa only [extraZero, Nat.add_zero] using outcome
  · by_cases needsPull : l.bits < l.op
    · exact packet.dolenLen_one_pull_length_semantics invariant
        buffers zero needsPull streamPtr statePtr whaveEq
        wsizeEq wnextEq windowEq dcodePtr codesGet safe mask
        extraWidth bitsBound left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize current
        beginLe span guard width lengthInput lengthBits
    · obtain ⟨used, consumed, slowNext, result, after,
        usedBound, consumedBound, run, packetNext,
        sourceNext, outcome⟩ :=
        packet.dolenLen_no_pull_length_semantics invariant
          buffers zero needsPull streamPtr statePtr whaveEq
          wsizeEq wnextEq windowEq dcodePtr codesGet safe mask
          extraWidth bitsBound left avail length outPtr outputPtr
          begPtr endPtr outputGet outputWrite outputSize current
          beginLe span guard width lengthInput lengthBits
      exact ⟨used, consumed, slowNext, result, after,
        by omega, consumedBound, run, packetNext,
        sourceNext, outcome⟩

#print axioms FastInputPacket.dolenLen_length_extra_semantics
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- The same translated length-link run exposes its physical second-level slice. -/
theorem FastInputPacket.dolen_link_default_state_exact_with_slice
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
      slice = (l.hold >>> codes[index].bits.toUInt32.toUInt64).toNat %
        2 ^ codes[index].op.toNat ∧
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
    ?_, rfl, rfl, rfl, rfl, rfl, resultPacket,
    invariant, codeBuffers, ?_⟩
  · simpa only [selected, afterCode, firstLocal, count, entry]
      using sliceEq
  · simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1

#print axioms FastInputPacket.dolen_link_default_state_exact_with_slice
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- The actual length-root link exports its physical second-level slice. -/
theorem FastInputPacket.dolen_root_link_default_state_with_slice
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
    packet.dolen_link_default_state_exact_with_slice invariant buffers
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

#print axioms FastInputPacket.dolen_root_link_default_state_with_slice
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inffast.Proofs

/-- The second-level index recorded by the translated length-link branch
is exactly the next independent bit-reader value. -/
theorem FastInputPacket.length_link_second_read
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

#print axioms FastInputPacket.length_link_second_read
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeShort
open Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable

/-- The actual two-level length lookup's physical link index and the
constructor-backed independent Huffman decode select the same leaf. -/
theorem FastInputPacket.length_selected_link_leaf_meaning
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
    (held : 15 ≤ slow.bits.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowNext,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      FastInputPacket h slowNext bs linked ∧
      stream slowNext bs = (stream slow bs).drop rootEntry.bits.toNat ∧
      (LeafAccepted LENS
        (codes.getD (baseOff + rootEntry.val.toNat + slice) default) →
        ∃ symbol,
          ValidSymbol LENS symbol ∧
          SymbolEntry LENS symbol
            (codes.getD (baseOff + rootEntry.val.toNat + slice) default) ∧
          rootEntry.bits.toNat +
            (codes.getD (baseOff + rootEntry.val.toNat + slice)
              default).bits.toNat = lens.getD symbol 0 ∧
          decodeSym lens (stream slow bs) =
            some (symbol, (stream slow bs).drop
              (rootEntry.bits.toNat +
                (codes.getD (baseOff + rootEntry.val.toNat + slice)
                  default).bits.toNat))) := by
  let rootEntry := codes.getD (baseOff + rootSlice) default
  obtain ⟨linked, slice, slowNext, firstRun, againL,
    sliceBound, sliceEq, linkedHere, targetLeaf, _,
    linkedPacket, _, _, sourceDrop⟩ :=
    packet.dolen_root_link_default_state_with_slice
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
  have secondRead := packet.length_link_second_read
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
  refine ⟨linked, slice, slowNext, firstRun, againL,
    linkedHere, linkedPacket, sourceDrop, ?_⟩
  intro accepted
  obtain ⟨symbol, valid, entryMeaning, codeLen,
    decoded, _⟩ := meaning.short (stream slow bs) target
      (rootEntry.bits.toNat + target.bits.toNat)
      (by rw [padding]; exact query) consumed
      accepted
  exact ⟨symbol, valid, entryMeaning,
    codeLen, decoded⟩

#print axioms FastInputPacket.length_selected_link_leaf_meaning
end Zlib.Inflate.Proofs

