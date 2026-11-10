import ZlibF.Proof.«inflate.c.payload-linked-eob-twopull-indexed-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096
theorem linked_eob_body_two_pull_of_decode_generic_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true ∧ result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, finish⟩ :=
    linked_eob_body_two_pull_indexed_generic_cursor
      packet invariant buffers small statePtr mode lcodePtr codesGet
      safe mask rootLink (L := lens) (D := D) (dict := dict)
      (history := history)
  let raw4 := third :: fourth :: fifth :: sixth :: rest
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    apply rootLink rootSlice root
    exact rootSliceEq
  have queryLink : IsLink LENS rootEntry = true :=
    (len_table_link_query safe root).mp link
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have decoded2 : decodeSym lens (stream slow2 raw4) =
      some (256, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2 selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink held2 decoded2 (by simp)
  have linkedEq : otherLinked = linked := by
    have same := otherRun.symm.trans linkRun
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
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  have selectedEnd := length_eob_entry_fields targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, token, cursor⟩ := finish selectedEnd decodedExact
  exact ⟨result, after, slowFinal, run, afterEq, broke,
    packetFinal, buffersFinal, token, cursor⟩

#print axioms linked_eob_body_two_pull_of_decode_generic_cursor
end Zlib.Inflate.Proofs
