import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Proof.«inftrees.c.decode.short»

namespace Zlib.Inftrees.Proofs.DecodeForward
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- Mathematical zero padding already has the full DEFLATE lookahead. -/
theorem padded_length (inp : List Bool) : 15 ≤ (DecodeShort.padded inp).length := by
  simp only [DecodeShort.padded, List.length_append, List.length_replicate]
  omega

/-- Padding cannot alter a word that already has fifteen bits. -/
theorem padded_of_long {inp : List Bool} (enough : 15 ≤ inp.length) : DecodeShort.padded inp = inp := by
  simp only [DecodeShort.padded, Nat.sub_eq_zero_of_le enough, List.replicate_zero, List.append_nil]

theorem padded_idempotent (inp : List Bool) : DecodeShort.padded (DecodeShort.padded inp) = DecodeShort.padded inp :=
  padded_of_long (padded_length inp)

/-- An installed root and its bounded subtables consume at most fifteen
bits on a real full-lookahead table query, including rejected leaves. -/
theorem tableRead_consumed_le_fifteen
    {type : UInt32} {ca : Array Code} {offset root used : Nat} {lens : List Nat}
    (inv : DecodeTableInvariant.Inv type ca offset root used lens)
    {inp : List Bool} {entry : Code} {consumed : Nat} (enough : 15 ≤ inp.length)
    (query : tableRead type ca offset root inp = some (entry, consumed)) : consumed ≤ 15 := by
  obtain ⟨i, suffix, rootRead, index, _source⟩ :=
    ZlibF.Math.InflateDecode.read_total root inp (by have := inv.rootTable.2.1; omega)
  obtain ⟨first, firstGet, firstPositive, firstBound⟩ := inv.rootTable.2.2.2 i index
  simp only [tableRead, rootRead, bind, Option.bind, firstGet] at query
  change (if Subtable.IsLink type first then do
    let (j, _) ← readBits first.op.toNat (inp.drop first.bits.toNat)
    let second ← ca[offset + first.val.toNat + j]?
    pure (second, first.bits.toNat + second.bits.toNat)
    else some (first, first.bits.toNat)) = some (entry, consumed) at query
  by_cases link : Subtable.IsLink type first = true
  · rw [ite_eq_left link] at query
    obtain ⟨_sameRoot, firstPositive, opPositive, totalBound, _extent, cells⟩ :=
      inv.subtables i first index firstGet link
    obtain ⟨j, tail, subRead, subIndex, _subSource⟩ :=
      ZlibF.Math.InflateDecode.read_total first.op.toNat (inp.drop first.bits.toNat)
        (by simp only [List.length_drop]; omega)
    obtain ⟨second, secondGet, secondPositive, secondBound⟩ := cells j subIndex
    simp only [subRead, bind, Option.bind, secondGet, pure] at query
    cases query
    omega
  · rw [ite_eq_right link] at query
    cases query
    have rootBound := inv.rootTable.2.1
    omega

/-- A valid independent symbol drives the installed LENS or DISTS table
forward, even when the real input is shorter than the root width. Padding
is only a query device: the returned code consumes bits of the original input. -/
theorem lookup_of_decode
    {type : UInt32} {ca : Array Code} {offset root used : Nat} {lens : List Nat}
    (inv : DecodeTableInvariant.Inv type ca offset root used lens)
    {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym lens inp = some (symbol, rest)) (valid : ValidSymbol type symbol) :
    ∃ entry consumed,
      tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) ∧
      LeafAccepted type entry ∧ SymbolEntry type symbol entry ∧
      consumed = lens.getD symbol 0 ∧ consumed ≤ inp.length ∧ rest = inp.drop consumed := by
  let padding := List.replicate (15 - inp.length) false
  have extended : decodeSym lens (DecodeShort.padded inp) = some (symbol, rest ++ padding) :=
    ZlibF.Spec.Proofs.ext_acceptable inv.acceptable inp symbol rest padding decoded
  obtain ⟨entry, consumed, query, classification⟩ := inv.classify (DecodeShort.padded inp) (padded_length inp)
  have accepted : LeafAccepted type entry := classification.mpr ⟨symbol, rest ++ padding, extended, valid⟩
  have bound := tableRead_consumed_le_fifteen inv (padded_length inp) query
  have doubleQuery : tableRead type ca offset root (DecodeShort.padded (DecodeShort.padded inp)) = some (entry, consumed) := by
    rw [padded_idempotent]
    exact query
  obtain ⟨selected, _selectedValid, meaning, length, selectedDecode, _extension⟩ :=
    inv.short (DecodeShort.padded inp) entry consumed doubleQuery (by have := padded_length inp; omega) accepted
  have symbols := congrArg Prod.fst (Option.some.inj (selectedDecode.symm.trans extended))
  dsimp only at symbols
  subst selected
  obtain ⟨_inside, _nonzero, wordPrefix, remaining⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
  have fit : lens.getD symbol 0 ≤ inp.length := by
    have prefixLength := wordPrefix.length_le
    simpa only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length] using prefixLength
  exact ⟨entry, consumed, query, accepted, meaning, length, by omega, by simpa only [length] using remaining⟩

#print axioms padded_length
#print axioms padded_of_long
#print axioms padded_idempotent
#print axioms tableRead_consumed_le_fifteen
#print axioms lookup_of_decode
end Zlib.Inftrees.Proofs.DecodeForward
