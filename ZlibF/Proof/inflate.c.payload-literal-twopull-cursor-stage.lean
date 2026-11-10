import ZlibF.Proof.«inflate.c.payload-literal-twopull-decoded-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- One actual two-pull literal token, direct or second-level table entry. -/
theorem FastInputPacket.fast_body_two_pull_literal_of_decode_generic_cursor
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
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {D : List Nat} {dict history : List UInt8}
    {symbol : Nat} {r1 : List Bool}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (symbol, r1))
    (smallSymbol : symbol < 256) :
    ∃ (byte : UInt8) (result : Zlib.Inffast.L) (after : Heap)
      (slowFinal : IL),
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      Space.get after dest = some (output.set! j byte) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: tail) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: tail) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: tail))
        (history ++ [byte]) false ∧
      result.in_ = inputAdvance l.in_ 2 := by
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
    exact linked_literal_body_two_pull_of_decode_generic_with_out_cursor
      packet invariant buffers small lcodePtr codesGet safe meaning
      mask rootLink left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard decoded smallSymbol
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
    have valid : ValidSymbol LENS symbol := by
      simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
    obtain ⟨_, _, _, _, restEq⟩ :=
      packet.two_pull_root_leaf_of_decode invariant buffers small
        lcodePtr codesGet safe meaning mask rfl noLink decoded valid
    have entryEq : codes.getD index default = codes[index] := by
      simp [Array.getD_eq_getD_getElem?, indexBound]
    have decodedExact : decodeSym lens
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
        some (symbol, (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: tail)).drop
            codes[index].bits.toNat) := by
      rw [entryEq] at restEq
      rw [← restEq]
      exact decoded
    obtain ⟨slowPrefix, slowFinal, result, after, run, out,
      afterEq, _, finalPacket, finalBuffers, token, cursor⟩ :=
      literal_body_two_pull_of_decode_generic_with_packet_cursor
        packet invariant buffers small lcodePtr codesGet safe meaning
        mask rfl noLink indexBound left avail outPtr outputPtr endPtr
        outputGet outputWrite outputSize current guard decodedExact smallSymbol
    have get : Space.get after dest = some
        (output.set! j codes[index].val.toUInt8) := by
      rw [afterEq]
      exact byte_view_get_put outputGet outputWrite _
    exact ⟨codes[index].val.toUInt8, result, after, slowFinal,
      run, out, get, finalPacket, finalBuffers, token, cursor⟩

#print axioms FastInputPacket.fast_body_two_pull_literal_of_decode_generic_cursor
end Zlib.Inflate.Proofs
