import ZlibF.Proof.«inflate.c.payload-linked-literal-indexed-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem linked_literal_body_no_pull_of_decode_generic_with_out_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    {used : Nat} {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : LenLink (codes.getD
      (baseOff + (l.hold &&& c.lmask.toUInt64).toNat) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs)
        (history ++ [byte]) false ∧
      result.in_ = l.in_ := by
  obtain ⟨selected, linked, rootSlice, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedPacket, linkedHere, finish⟩ :=
    linked_literal_body_no_pull_indexed_generic_with_out_cursor
      packet invariant buffers held lcodePtr codesGet safe mask rootLink
      left avail outPtr outputPtr endPtr outputGet outputWrite outputSize
      current guard (L := lens) (D := D) (dict := dict) (history := history)
  let rootEntry := codes.getD (baseOff + rootSlice) default
  have root : rootSlice < 2 ^ rootWidth := by
    rw [rootSliceEq, Zlib.Inffast.Proofs.u64_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have link : LenLink rootEntry := by
    simpa only [rootEntry, rootSliceEq] using rootLink
  have queryLink : IsLink LENS rootEntry = true :=
    (payload_len_table_link_query safe root).mp link
  have selectedHold : selected.hold = l.hold := by
    exact selectedPacket.hold.trans packet.hold.symm
  have rootIndex : rootSlice = selected.hold.toNat % 2 ^ rootWidth := by
    rw [rootSliceEq, selectedHold,
      Zlib.Inffast.Proofs.u64_and_mask mask]
  have heldNat : 15 ≤ slow.bits.toNat := by
    have noSmall : ¬ slow.bits.toNat < 15 := by
      intro small
      apply held
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    omega
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.payload_length_selected_link_match_of_decode
      invariant buffers selectedHere lcodePtr codesGet safe meaning
      root rootIndex link queryLink heldNat decoded (by omega)
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
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow bs).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens (stream slow bs) =
      some (symbol, (stream slow bs).drop
        (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, out, get, packetFinal,
    buffersFinal, _, token, cursor⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, out, get, packetFinal, buffersFinal, token, cursor⟩

#print axioms linked_literal_body_no_pull_of_decode_generic_with_out_cursor
end Zlib.Inflate.Proofs
