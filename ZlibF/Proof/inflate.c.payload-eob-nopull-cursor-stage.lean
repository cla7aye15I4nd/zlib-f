import ZlibF.Proof.«inflate.c.payload-linked-eob-nopull-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One no-refill end-of-block token, whether the actual length root is direct or linked. -/
theorem FastInputPacket.fast_body_no_pull_eob_of_decode_generic_cursor
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
    (rootFits : rootWidth ≤ slow.bits.toNat)
    {D : List Nat} {dict history : List UInt8} {r1 : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (256, r1)) :
    ∃ (result : Zlib.Inffast.L) (after : Heap) (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧
      FastInputPacket after slowFinal bs result ∧
      DispatchBuffers after r slowFinal bs ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow bs) (stream slowFinal bs) history true ∧ result.in_ = l.in_ := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have maskIndex : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [maskIndex]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  by_cases link : LenLink (codes.getD (baseOff + rootSlice) default)
  · exact linked_eob_body_no_pull_of_decode_generic_cursor
      packet invariant buffers held statePtr mode lcodePtr codesGet
      safe meaning mask link decoded
  · have noLink : IsLink LENS
        (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false := by
      cases hq : IsLink LENS (codes.getD (baseOff + rootSlice) default) with
      | false => simpa only [← maskIndex] using hq
      | true => exact False.elim (link ((payload_len_table_link_query safe root).mpr hq))
    have heldNat : 15 ≤ slow.bits.toNat := by
      have noSmall : ¬ slow.bits.toNat < 15 := by
        intro small
        apply held
        rw [packet.bits]
        exact UInt32.lt_iff_toNat_lt.mpr small
      omega
    obtain ⟨_, _, _, restEq⟩ :=
      packet.length_root_leaf_of_decode meaning rootFits heldNat
        noLink decoded (by simp [ValidSymbol])
    let index := baseOff + rootSlice
    have indexBound : index < codes.size := by
      have rootSize := safe.2.1
      omega
    have entryEq : codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth)
        default = codes[index] := by
      rw [← maskIndex]
      simp [index, Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens (stream slow bs) =
        some (256, (stream slow bs).drop codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨result, after, slowFinal, run, afterEq, broke,
      _, inputSlice, finalPacket, finalBuffers, token⟩ :=
      eob_body_no_pull_of_decode_generic_with_packet
        packet invariant buffers held heldNat statePtr mode lcodePtr
        rfl codesGet meaning mask rootFits noLink indexBound
        decodedExact
    exact ⟨result, after, slowFinal, run, afterEq, broke,
      finalPacket, finalBuffers, token,
      finalPacket.cursor.trans (inputSlice.sameCursor.trans packet.cursor.symm)⟩

#print axioms FastInputPacket.fast_body_no_pull_eob_of_decode_generic_cursor
end Zlib.Inflate.Proofs
