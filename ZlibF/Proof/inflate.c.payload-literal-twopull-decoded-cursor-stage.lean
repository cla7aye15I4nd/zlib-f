import ZlibF.Proof.«inflate.c.payload-literal-twopull-base-cursor-stage»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
theorem literal_body_two_pull_of_decode_generic_with_packet_cursor
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
    (noLink : IsLink LENS
      (codes.getD (baseOff +
        (((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64)).toNat %
            2 ^ rootWidth)) default) = false)
    (indexBound : index < codes.size)
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
    {D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym lens
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
 :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      FastInputPacket after slowFinal
        (third :: fourth :: fifth :: sixth :: rest) result ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step lens D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false ∧
      result.in_ = inputAdvance l.in_ 2 := by
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using (show symbol ≤ 285 by omega)
  obtain ⟨_, fitsD, widthD, meaningD, _⟩ :=
    packet.two_pull_root_leaf_of_decode invariant buffers small
      lcodePtr codesGet safe meaning mask indexEq noLink decoded valid
  have entryEq : codes.getD index default = codes[index] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16 := by
    simpa only [entryEq] using fitsD
  have codeWidth : codes[index].bits.toNat ≤ 15 := by
    simpa only [entryEq] using widthD
  have meaningIndex : SymbolEntry LENS symbol codes[index] := by
    simpa only [entryEq] using meaningD
  obtain ⟨literal, value⟩ :=
    length_literal_entry_fields smallSymbol meaningIndex
  exact literal_body_two_pull_generic_with_packet_cursor packet invariant buffers small
    lcodePtr codesGet safe mask indexEq indexBound codeFits codeWidth
    literal left avail outPtr outputPtr endPtr outputGet
    outputWrite outputSize current guard decoded smallSymbol value

#print axioms literal_body_two_pull_of_decode_generic_with_packet_cursor
end Zlib.Inflate.Proofs
