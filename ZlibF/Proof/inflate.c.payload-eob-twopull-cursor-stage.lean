import ZlibF.Proof.«inflate.c.payload-linked-eob-twopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One actual two-pull end-of-block token, direct or second-level table entry. -/
theorem FastInputPacket.fast_body_two_pull_eob_of_decode_generic_cursor
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
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: tail) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: tail) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: tail))
        history true ∧ result.in_ = inputAdvance l.in_ 2 := by
  let filledHold : UInt64 :=
    (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
      (second.toUInt64 <<< (l.bits + 8).toUInt64)
  let rootSlice := (filledHold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = filledHold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · have rootLink : ∀ k, k < 2 ^ rootWidth →
        (k = (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
            c.lmask.toUInt64).toNat) →
        LenLink (codes.getD (baseOff + k) default) := by
      intro k _ eq
      simpa only [eq, rootSlice, filledHold] using link
    exact linked_eob_body_two_pull_of_decode_generic_cursor
      packet invariant buffers small statePtr mode lcodePtr codesGet
      safe meaning mask rootLink decoded
  · have noLink : IsLink LENS
        (codes.getD (baseOff + filledHold.toNat % 2 ^ rootWidth)
          default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((len_table_link_query safe root).mpr hq))
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    obtain ⟨_, _, _, _, restEq⟩ :=
      packet.two_pull_root_leaf_of_decode invariant buffers small
        lcodePtr codesGet safe meaning mask rfl noLink decoded
        (by simp [ValidSymbol])
    have entryEq : codes.getD index default = codes[index] := by
      simp [Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
        some (256, (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
            codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨slowPrefix, slowFinal, result, after, run, afterEq,
      broke, _, _, finalPacket, finalBuffers, token, cursor⟩ :=
      eob_body_two_pull_of_decode_generic_with_packet_cursor
        packet invariant buffers small statePtr mode lcodePtr codesGet
        safe meaning mask rfl noLink indexBound decodedExact
    exact ⟨result, after, slowFinal, run, afterEq, broke,
      finalPacket, finalBuffers, token, cursor⟩

#print axioms FastInputPacket.fast_body_two_pull_eob_of_decode_generic_cursor
end Zlib.Inflate.Proofs
