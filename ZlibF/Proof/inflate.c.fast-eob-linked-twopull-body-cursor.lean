import ZlibF.Proof.«inflate.c.fast-eob-nopull-body-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- The actual two-pull linked EOB body retains its entry output cursor. -/
theorem FastInputPacket.fast_body_linked_eob_two_pull_output_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat)
    {rest : List Bool}
    (decoded : decodeSym lens (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (256, rest)) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = l.out := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    selectedOut, holdFrame, _, leftFrame, _, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootLink2 : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have selectedHere : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  have selectedOutPtr : selected.out = .ref dest j :=
    selectedOut.trans outPtr
  have cursorBound2 : j ≤ oo + slow2.left.toNat := by
    rw [leftFrame]
    exact cursorBound
  obtain ⟨linked, slice, firstRun, againL, sliceBound,
    linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_output_cursor invariant
      buffers2 statePtr mode selectedHere lcodePtr codesGet
      safe rootBound rootLink2 (by omega) selectedOutPtr outputGet
      cursorBound2
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe rootBound).mp rootLink2
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    have selectedHold : selected.hold = fast2.hold := by rw [selectedEq]
    rw [rootSliceEq, selectedHold]
    exact Zlib.Inffast.Proofs.u64_and_mask mask
  have decoded2 : decodeSym lens
      (stream slow2 (third :: fourth :: fifth :: sixth :: tail)) =
      some (256, rest) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2 selectedHere lcodePtr codesGet safe meaning
      rootBound rootIndex rootLink2 queryLink (by omega) decoded2 (by simp)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans firstRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff + rootEntry.val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff + rootEntry.val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS 256 target := by
    simpa only [target, rootEntry, sliceEq] using otherMeaning
  have selectedEnd := length_eob_entry_fields targetMeaning
  obtain ⟨result, after, array, next, loopRun, resultOut,
    _, _, _, _, nextEq⟩ := finish selectedEnd
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) :=
    body_from_two_pull_root needsPull prefixRun loopRun
  refine ⟨result, after, bodyRun, ?_⟩
  rw [nextEq] at resultOut
  exact resultOut.trans outPtr.symm

#print axioms FastInputPacket.fast_body_linked_eob_two_pull_output_cursor
end Zlib.Inflate.Proofs
