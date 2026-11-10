import ZlibF.Proof.«inflate.c.slow-input-fragment»
import ZlibF.Proof.Format.Deflate
import ZlibF.Proof.«inftrees.c.decode.semantics»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs ZlibF.Spec.Proofs
set_option autoImplicit false

/-- If the independently decoded code word fits the supplied prefix,
the independent decoder already returns that same symbol there. This
requires no table or prefix-free hypothesis. -/
theorem decodeSym_restrict {L : List Nat} {available future rest : List Bool} {symbol : Nat}
    (decoded : decodeSym L (available ++ future) = some (symbol, rest))
    (fits : L.getD symbol 0 ≤ available.length) :
    decodeSym L available = some (symbol, available.drop (L.getD symbol 0)) ∧
      rest = available.drop (L.getD symbol 0) ++ future := by
  have details := Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
  have word : codeOf L symbol <+: available := List.prefix_of_prefix_length_le details.2.2.1
    (List.prefix_append available future) (by simpa only [codeOf, natToBitsMSB_length] using fits)
  unfold decodeSym at decoded ⊢
  cases found : (List.range L.length).find? (fun a => L.getD a 0 != 0 && (codeOf L a).isPrefixOf (available ++ future)) with
  | none => simp only [found] at decoded; cases decoded
  | some selected =>
    simp only [found, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    obtain ⟨tested, earlier, later, split, excluded⟩ := List.find?_eq_some_iff_append.mp found
    have selectedTest : (L.getD selected 0 != 0 && (codeOf L selected).isPrefixOf available) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨details.2.1, List.isPrefixOf_iff_prefix.mpr word⟩
    have localFound : (List.range L.length).find? (fun a => L.getD a 0 != 0 && (codeOf L a).isPrefixOf available) = some selected := by
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨selectedTest, earlier, later, split, ?_⟩
      intro a member
      have forbidden := excluded a member
      cases accepted : (L.getD a 0 != 0 && (codeOf L a).isPrefixOf available) with
      | false => rfl
      | true =>
        have acceptedFields : (L.getD a 0 != 0) = true ∧ (codeOf L a).isPrefixOf available = true := by
          simpa only [Bool.and_eq_true] using accepted
        have extended : (L.getD a 0 != 0 && (codeOf L a).isPrefixOf (available ++ future)) = true := by
          rw [Bool.and_eq_true]
          exact ⟨acceptedFields.1, List.isPrefixOf_iff_prefix.mpr
            ((List.isPrefixOf_iff_prefix.mp acceptedFields.2).trans (List.prefix_append available future))⟩
        rw [extended] at forbidden
        contradiction
    rw [localFound]
    exact ⟨rfl, List.drop_append_of_le_length fits⟩

/-- Fixed-width independent reads also restrict exactly to the supplied
prefix as soon as their whole width is present. -/
theorem readBits_restrict {n value : Nat} {available future rest : List Bool}
    (read : readBits n (available ++ future) = some (value, rest)) (fits : n ≤ available.length) :
    ∃ localRest, readBits n available = some (value, localRest) ∧ rest = localRest ++ future := by
  induction n generalizing available value rest with
  | zero =>
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨available, rfl, rfl⟩
  | succ n ih =>
    cases available with
    | nil => simp only [List.length_nil] at fits; omega
    | cons bit available =>
      simp only [List.cons_append, readBits] at read
      cases previous : readBits n (available ++ future) with
      | none => rw [previous] at read; cases read
      | some pair =>
        obtain ⟨oldValue, oldRest⟩ := pair
        obtain ⟨localRest, localRead, suffix⟩ := ih previous (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using fits)
        rw [previous] at read
        simp only [Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        refine ⟨localRest, ?_, suffix⟩
        simp only [readBits, localRead]

#print axioms decodeSym_restrict
#print axioms readBits_restrict
end Zlib.Inflate.Proofs.SlowInputFragment
