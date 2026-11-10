import ZlibF.Proof.«inflate.c.fast-eob-linked-output-cursor»
import ZlibF.Proof.«inflate.c.payload-valid-body-cursor-stage»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

/-- A linked EOB reached without the initial two pulls leaves the actual
fast-body output cursor unchanged. The subtable index is proved by the
independent decoder and the installed table invariant. -/
theorem FastInputPacket.fast_body_linked_eob_no_pull_output_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat)
    {rest : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (256, rest))
    :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = l.out := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedHere : selected.here =
      .ref codeRef (baseOff + rootSlice) := rfl
  have root : rootSlice < 2 ^ rootWidth := by
    rw [show rootSlice = l.hold.toNat % 2 ^ rootWidth from
      Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    exact rootLink
  have queryLink : IsLink LENS
      (codes.getD (baseOff + rootSlice) default) = true :=
    (len_table_link_query safe root).mp link
  have heldNat : 15 ≤ slow.bits.toNat := by
    have noSmall : ¬ slow.bits.toNat < 15 := by
      intro small
      apply held
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    omega
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    change (l.hold &&& c.lmask.toUInt64).toNat =
      l.hold.toNat % 2 ^ rootWidth
    exact Zlib.Inffast.Proofs.u64_and_mask mask
  obtain ⟨linked, slice, firstRun, againL, sliceBound,
    linkedHere, finish⟩ :=
    selectedPacket.dolen_linked_end_output_cursor invariant
      buffers statePtr mode selectedHere lcodePtr codesGet
      safe root link heldNat outPtr outputGet cursorBound
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.payload_length_selected_link_match_of_decode
      invariant buffers selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink heldNat decoded (by simp)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans firstRun
    cases same
    rfl
  have sliceEq : otherSlice = slice := by
    have ptrEq :
        (Ptr.ref codeRef (baseOff +
          (codes.getD (baseOff + rootSlice) default).val.toNat + otherSlice) : CodePtr) =
        .ref codeRef (baseOff +
          (codes.getD (baseOff + rootSlice) default).val.toNat + slice) := by
      exact otherHere.symm.trans (by rw [linkedEq]; exact linkedHere)
    injection ptrEq with offEq
    omega
  let target := codes.getD
    (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS 256 target := by
    simpa only [target, sliceEq] using otherMeaning
  have selectedEnd := length_eob_entry_fields targetMeaning
  obtain ⟨result, after, array, next, loopRun, resultOut,
    _, _, _, _, nextEq⟩ := finish selectedEnd
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) :=
    body_from_no_pull_root held lcodePtr codesGet
      (by have rootSize := safe.2.1; omega) rfl rfl loopRun
  refine ⟨result, after, bodyRun, ?_⟩
  rw [nextEq] at resultOut
  exact resultOut.trans outPtr.symm

#print axioms FastInputPacket.fast_body_linked_eob_no_pull_output_cursor
end Zlib.Inflate.Proofs
