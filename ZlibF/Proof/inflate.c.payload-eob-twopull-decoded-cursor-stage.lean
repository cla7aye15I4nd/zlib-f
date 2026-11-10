import ZlibF.Proof.«inflate.c.payload-eob-twopull-base-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem eob_body_two_pull_of_decode_generic_with_packet_cursor
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
    {baseOff rootWidth index used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (noLinkQuery : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
    {D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true ∧ result.in_ = inputAdvance l.in_ 2 := by
  have valid : ValidSymbol LENS 256 := by
    simp [ValidSymbol]
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLinkQuery decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS 256 codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨nonzero, notBase, notLink, endCode⟩ :=
    length_eob_entry_fields meaningIndex
  exact eob_body_two_pull_generic_with_packet_cursor packet invariant buffers small
    statePtr mode lcodePtr codesGet safe mask indexEq indexBound
    codeFits codeWidth nonzero notBase notLink endCode decoded

#print axioms eob_body_two_pull_of_decode_generic_with_packet_cursor
end Zlib.Inflate.Proofs
