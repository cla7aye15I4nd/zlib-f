import ZlibF.Proof.«inflate.c.fast-eob-linked-twopull-body-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.fast_body_two_pull_eob_output_cursor
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
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat)
    {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (256, r1)) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = l.out := by
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
    exact packet.fast_body_linked_eob_two_pull_output_cursor
      invariant buffers small statePtr mode lcodePtr codesGet
      safe meaning mask rootLink outPtr outputGet cursorBound decoded
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
      broke, out, _, finalPacket, finalBuffers, token⟩ :=
      eob_body_two_pull_of_decode_generic_with_packet
        packet invariant buffers small statePtr mode lcodePtr codesGet
        safe meaning mask rfl noLink indexBound
        (D := []) (dict := []) (history := []) decodedExact
    exact ⟨result, after, run, out⟩


#print axioms FastInputPacket.fast_body_two_pull_eob_output_cursor
end Zlib.Inflate.Proofs
