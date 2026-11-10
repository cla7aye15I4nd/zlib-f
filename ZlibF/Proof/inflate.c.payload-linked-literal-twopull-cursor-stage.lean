import ZlibF.Proof.«inflate.c.payload-linked-literal-twopull-indexed-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem linked_literal_body_two_pull_of_decode_generic_with_out_cursor
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
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8} {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [byte]) false ∧
      result.in_ = inputAdvance l.in_ 2 := by
  obtain ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, selectedHere, rootSliceEq,
    selectedHold, selectedPacket, buffers2, source2, held2,
    linkedHere, finish⟩ :=
    linked_literal_body_two_pull_indexed_generic_with_out_cursor
      packet invariant buffers small lcodePtr codesGet safe mask
      rootLink left avail outPtr outputPtr endPtr
      outputGet outputWrite outputSize current guard
      (L := lens) (D := D) (dict := dict) (history := history)
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
      some (symbol, r1) := by
    rw [source2]
    exact decoded
  obtain ⟨otherLinked, otherSlice, _, otherRun, _,
    otherHere, _, _, otherSliceEq, otherMeaning, otherRest⟩ :=
    selectedPacket.length_selected_link_match_of_decode
      invariant buffers2
      selectedHere lcodePtr codesGet safe meaning root rootIndex
      link queryLink held2 decoded2 (by omega)
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
  have actualSliceEq : slice =
      (selected.hold >>> rootEntry.bits.toUInt32.toUInt64).toNat %
        2 ^ rootEntry.op.toNat := by
    rw [← sliceEq]
    exact otherSliceEq
  let target := codes.getD (baseOff + rootEntry.val.toNat + slice) default
  have targetMeaning : SymbolEntry LENS symbol target := by
    simpa only [rootEntry, target, sliceEq] using otherMeaning
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol targetMeaning
  have codeRest : r1 = (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
      (rootEntry.bits.toNat + target.bits.toNat) := by
    rw [source2] at otherRest
    simpa only [rootEntry, target, sliceEq] using otherRest
  have decodedExact : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol, (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          (rootEntry.bits.toNat + target.bits.toNat)) := by
    rw [← codeRest]
    exact decoded
  obtain ⟨result, after, slowFinal, run, out, get, packetFinal,
    buffersFinal, token, cursor⟩ :=
    finish symbol literal decodedExact smallSymbol value
  exact ⟨target.val.toUInt8, result, after, slowFinal,
    run, out, get, packetFinal, buffersFinal, token, cursor⟩

#print axioms linked_literal_body_two_pull_of_decode_generic_with_out_cursor
end Zlib.Inflate.Proofs
