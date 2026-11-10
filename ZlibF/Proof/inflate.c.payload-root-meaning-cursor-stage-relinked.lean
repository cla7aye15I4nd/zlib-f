import ZlibF.Proof.«inflate.c.payload-body-two-linked-cursor-stage-relinked»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 4096

theorem FastInputPacket.payload_length_root_match_of_decode
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs l)
    {codes : Array Code} {baseOff rootWidth used : Nat}
    {lens : List Nat}
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (rootFits : rootWidth ≤ slow.bits.toNat)
    (held : 15 ≤ slow.bits.toNat)
    (noLink : IsLink LENS
      (codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default) = false)
    {symbol : Nat} {rest : List Bool}
    (decoded : decodeSym lens (stream slow bs) = some (symbol, rest))
    (lengthMin : 257 ≤ symbol) (lengthMax : symbol ≤ 285) :
    let entry := codes.getD (baseOff + l.hold.toNat % 2 ^ rootWidth) default
    LeafAccepted LENS entry ∧ SymbolEntry LENS symbol entry ∧
      entry.op &&& 16 ≠ 0 ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      rest = (stream slow bs).drop entry.bits.toNat := by
  let slice := l.hold.toNat % 2 ^ rootWidth
  let entry := codes.getD (baseOff + slice) default
  let inp := stream slow bs
  have valid : ValidSymbol LENS symbol := by
    simpa [ValidSymbol] using lengthMax
  have long : 15 ≤ inp.length := by
    simp only [inp, stream, List.length_append, natBits_length]
    omega
  have rootBound : baseOff + slice < codes.size := by
    have rootSize := meaning.rootTable.2.2.1
    have modBound : slice < 2 ^ rootWidth :=
      Nat.mod_lt _ (Nat.pow_pos (by omega))
    omega
  have rootRead : readBits rootWidth inp =
      some (slice, inp.drop rootWidth) := by
    have read := readBits_held_stream slow bs rootWidth rootFits
    simpa only [inp, slice, ← packet.hold] using read
  have cell : codes[baseOff + slice]? = some entry := by
    simp [entry, Array.getD_eq_getD_getElem?, rootBound]
  have noLinkCode :
      (entry.op != 0 && (entry.op &&& 0xf0) == 0) = false := by
    simpa [IsLink, entry, slice] using noLink
  have queryRoot : tableRead LENS codes baseOff rootWidth inp =
      some (entry, entry.bits.toNat) := by
    simp only [tableRead, rootRead, bind, Option.bind, cell]
    simp only [noLinkCode]
    simp
  obtain ⟨other, count, query, classification⟩ :=
    meaning.classify inp long
  have acceptedOther : LeafAccepted LENS other :=
    classification.mpr ⟨symbol, rest, decoded, valid⟩
  have same : (other, count) = (entry, entry.bits.toNat) :=
    Option.some.inj (query.symm.trans queryRoot)
  have accepted : LeafAccepted LENS entry := by
    simpa only [(Prod.mk.inj same).1] using acceptedOther
  obtain ⟨found, _, foundMeaning, width, foundDecode⟩ :=
    packet.payload_length_root_leaf_meaning meaning rootFits held rootBound
      noLink accepted
  have decodedEq := Option.some.inj (foundDecode.symm.trans decoded)
  have symbolEq : found = symbol := congrArg Prod.fst decodedEq
  have restEq : rest = inp.drop entry.bits.toNat :=
    (congrArg Prod.snd decodedEq).symm
  subst found
  have base := (payload_length_base_symbol_fields_view lengthMin lengthMax
    foundMeaning).1
  exact ⟨accepted, foundMeaning, base, width, restEq⟩

#print axioms FastInputPacket.payload_length_root_match_of_decode
end Zlib.Inflate.Proofs
