import ZlibF.Proof.«inffixed.h.meaning»

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Zlib.InffixedH.Proofs
open C ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

/-- Every five-bit fixed distance lookup has the independent canonical
distance meaning, including the two reserved, rejected symbols. -/
theorem distfix_full_input (inp : List Bool) (enough : 5 ≤ inp.length) :
    ∃ (symbol : Nat) (rest : List Bool) (entry : Code),
      decodeSym fixedDistLens inp = some (symbol, rest) ∧
      tableRead DISTS Zlib.InffixedH.distfix 0 5 inp =
        some (entry, entry.bits.toNat) ∧
      entry.bits.toNat = fixedDistLens.getD symbol 0 ∧
      rest = inp.drop entry.bits.toNat ∧
      SymbolEntry DISTS symbol entry ∧
      (LeafAccepted DISTS entry ↔ ValidSymbol DISTS symbol) := by
  obtain ⟨i, suffix, _read, bound, source⟩ :=
    ZlibF.Math.InflateDecode.read_total 5 inp enough
  have inside : i < 32 := by simpa using bound
  have cell := fixedDistCellCorrect_all ⟨i, inside⟩
  cases decoded : decodeSym fixedDistLens (bitsOfNat i 5) with
  | none => simp [fixedDistCellCorrect, decoded] at cell
  | some value =>
      obtain ⟨symbol, prefixRest⟩ := value
      cases selected : Zlib.InffixedH.distfix[i]? with
      | none => simp [fixedDistCellCorrect, decoded, selected] at cell
      | some entry =>
          simp only [fixedDistCellCorrect, decoded, selected] at cell
          obtain ⟨restPrefix, length, meaning, accepted⟩ := cell
          have decodedFull : decodeSym fixedDistLens inp =
              some (symbol, prefixRest ++ suffix) := by
            rw [source]
            exact ZlibF.Spec.Proofs.ext_fixedDist
              (bitsOfNat i 5) symbol prefixRest suffix decoded
          have used : entry.bits.toNat ≤ 5 := by
            have hprefix := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.2.1
            have h := hprefix.length_le
            simpa only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length,
              bitsOfNat_length, ← length] using h
          have restFull : prefixRest ++ suffix = inp.drop entry.bits.toNat := by
            calc
              prefixRest ++ suffix = (bitsOfNat i 5).drop entry.bits.toNat ++ suffix := by
                rw [restPrefix]
              _ = (bitsOfNat i 5 ++ suffix).drop entry.bits.toNat :=
                (List.drop_append_of_le_length (by simpa only [bitsOfNat_length] using used)).symm
              _ = inp.drop entry.bits.toNat := by rw [source]
          have noLink : ((entry.op &&& 0xf0) == 0) = false := by
            have h := distfix_no_links ⟨i, inside⟩
            have entryEq : Zlib.InffixedH.distfix[i]! = entry := by
              simp [getElem!_def, selected]
            rw [entryEq] at h
            simpa using h
          have noLinkProp : entry.op &&& 0xf0 ≠ 0 := by
            simpa using noLink
          have query : tableRead DISTS Zlib.InffixedH.distfix 0 5 inp =
              some (entry, entry.bits.toNat) := by
            rw [source]
            simp [tableRead, DISTS, LENS, readBits_bitsOfNat,
              Nat.mod_eq_of_lt bound, selected, noLinkProp]
          exact ⟨symbol, prefixRest ++ suffix, entry, decodedFull, query,
            length, restFull, meaning, accepted⟩

/-- Every nine-bit fixed literal/length lookup has the independent canonical
literal, end, length, or reserved-symbol meaning. -/
theorem lenfix_full_input (inp : List Bool) (enough : 9 ≤ inp.length) :
    ∃ (symbol : Nat) (rest : List Bool) (entry : Code),
      decodeSym fixedLitLens inp = some (symbol, rest) ∧
      tableRead LENS Zlib.InffixedH.lenfix 0 9 inp =
        some (entry, entry.bits.toNat) ∧
      entry.bits.toNat = fixedLitLens.getD symbol 0 ∧
      rest = inp.drop entry.bits.toNat ∧
      SymbolEntry LENS symbol entry ∧
      (LeafAccepted LENS entry ↔ ValidSymbol LENS symbol) := by
  obtain ⟨i, suffix, _read, bound, source⟩ :=
    ZlibF.Math.InflateDecode.read_total 9 inp enough
  have inside : i < 512 := by simpa using bound
  have cell := fixedLitCellCorrect_all ⟨i, inside⟩
  cases decoded : decodeSym fixedLitLens (bitsOfNat i 9) with
  | none =>
      unfold fixedLitCellCorrect at cell
      simp only [decoded] at cell
  | some value =>
      obtain ⟨symbol, prefixRest⟩ := value
      cases selected : Zlib.InffixedH.lenfix[i]? with
      | none =>
          unfold fixedLitCellCorrect at cell
          simp only [decoded, selected] at cell
      | some entry =>
          unfold fixedLitCellCorrect at cell
          simp only [decoded, selected] at cell
          obtain ⟨restPrefix, length, meaning, accepted⟩ := cell
          have decodedFull : decodeSym fixedLitLens inp =
              some (symbol, prefixRest ++ suffix) := by
            rw [source]
            exact ZlibF.Spec.Proofs.ext_fixedLit
              (bitsOfNat i 9) symbol prefixRest suffix decoded
          have used : entry.bits.toNat ≤ 9 := by
            have hprefix := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.2.1
            have h := hprefix.length_le
            simpa only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length,
              bitsOfNat_length, ← length] using h
          have restFull : prefixRest ++ suffix = inp.drop entry.bits.toNat := by
            calc
              prefixRest ++ suffix = (bitsOfNat i 9).drop entry.bits.toNat ++ suffix := by
                rw [restPrefix]
              _ = (bitsOfNat i 9 ++ suffix).drop entry.bits.toNat :=
                (List.drop_append_of_le_length (by simpa only [bitsOfNat_length] using used)).symm
              _ = inp.drop entry.bits.toNat := by rw [source]
          have noLink : (entry.op != 0 && (entry.op &&& 0xf0) == 0) = false := by
            have h := lenfix_no_links ⟨i, inside⟩
            have entryEq : Zlib.InffixedH.lenfix[i]! = entry := by
              simp [getElem!_def, selected]
            rw [entryEq] at h
            exact Bool.eq_false_iff.mpr h
          have noLinkProp : ¬ (entry.op ≠ 0 ∧ entry.op &&& 0xf0 = 0) := by
            simpa using noLink
          have query : tableRead LENS Zlib.InffixedH.lenfix 0 9 inp =
              some (entry, entry.bits.toNat) := by
            rw [source]
            simp [tableRead, LENS, readBits_bitsOfNat,
              Nat.mod_eq_of_lt bound, selected, noLinkProp]
          exact ⟨symbol, prefixRest ++ suffix, entry, decodedFull, query,
            length, restFull, meaning, accepted⟩

end Zlib.InffixedH.Proofs
