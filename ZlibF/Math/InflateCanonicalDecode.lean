import ZlibF.Math.InflateDecodeBits
import ZlibF.Proof.Format.Huffman

/-! Heap-free inverse facts for the constructor's symbol order. -/

set_option autoImplicit false

namespace ZlibF.Math.InflateDecode
open ZlibF.Spec Zlib.Inftrees.Proofs Zlib.Inftrees

/-- A symbol occurs at most once in the constructor's nonzero-length
allocation order. Different length groups are disjoint. -/
theorem allocation_order_nodup (f : Nat → Nat) (n l : Nat) :
    (wsAux f n l).Nodup := by
  induction l with
  | zero => exact List.nodup_nil
  | succ l ih =>
      rw [wsAux, List.nodup_append]
      refine ⟨ih, ?_, ?_⟩
      · exact List.Pairwise.filter _ List.nodup_range
      · intro a ha b hb same
        subst b
        have previous := (mem_wsAux.mp ha).2.2
        have current := (mem_fl.mp hb).2
        omega

/-- Equality of two allocated symbols identifies their allocation index. -/
theorem allocation_index_injective (f : Nat → Nat) (n : Nat) {i j : Nat}
    (hi : i < Tc f n 15) (hj : j < Tc f n 15)
    (same : Canon.sy (lensOf f n) i = Canon.sy (lensOf f n) j) : i = j := by
  have left : i < (wsAux f n 15).length := by rwa [wsAux_length]
  have right : j < (wsAux f n 15).length := by rwa [wsAux_length]
  simp only [Canon.sy, ord_eq] at same
  exact (List.Nodup.getD_inj left right (allocation_order_nodup f n 15)).mp same

/-- The code of an allocated symbol is its retained constructor word.
No Kraft, completeness or Fits assumption is needed for this identity. -/
theorem allocated_word_code (f : Nat → Nat) (n : Nat) {j : Nat}
    (index : j < Tc f n 15) :
    codeOf (lensOf f n) (Canon.sy (lensOf f n) j) =
      Zlib.Inffast.Proofs.bitsOfNat (Canon.H (lensOf f n) j)
        (Canon.L (lensOf f n) j) := by
  have listIndex : j < Canon.nz (lensOf f n) := by rwa [nz_eq]
  have bounds := Canon.L_interval (lensOf f n) listIndex
  have inside : Canon.sy (lensOf f n) j < n := by
    simpa only [lensOf_length] using bounds.2.2.2.2
  have length : f (Canon.sy (lensOf f n) j) = Canon.L (lensOf f n) j := by
    exact (lensOf_getD f inside).symm
  obtain ⟨q, qIndex, same, _qLength, code⟩ :=
    allocated_symbol_code f n (Canon.sy (lensOf f n) j) inside
      (by rw [length]; exact bounds.1) (by rw [length]; exact bounds.2.1)
  have sameIndex : q = j := allocation_index_injective f n qIndex index same
  subst q
  simpa only [length] using code

/-- An acceptable alphabet decodes one of its nonempty canonical words,
retaining every trailing suffix. This uses only independent prefix freedom. -/
theorem decode_canonical_word {kind : CodeKind} {lens : List Nat}
    (acceptable : Acceptable kind lens) (symbol : Nat)
    (nonzero : lens.getD symbol 0 ≠ 0) (suffix : List Bool) :
    decodeSym lens (codeOf lens symbol ++ suffix) = some (symbol, suffix) := by
  let inp := codeOf lens symbol ++ suffix
  have inside := Proofs.getD_ne_zero_lt lens symbol nonzero
  have symbolPrefix : codeOf lens symbol <+: inp := List.prefix_append _ _
  have selected : (lens.getD symbol 0 != 0 && (codeOf lens symbol).isPrefixOf inp) = true := by
    rw [List.isPrefixOf_iff_prefix.mpr symbolPrefix]
    simp only [Bool.and_true, bne_iff_ne]
    exact nonzero
  have found : ∃ candidate : Nat, (List.range lens.length).find?
      (fun k => lens.getD k 0 != 0 && (codeOf lens k).isPrefixOf inp) = some candidate := by
    cases result : (List.range lens.length).find?
        (fun k => lens.getD k 0 != 0 && (codeOf lens k).isPrefixOf inp) with
    | some candidate => exact ⟨candidate, rfl⟩
    | none =>
        have absent := List.find?_eq_none.mp result symbol (List.mem_range.mpr inside)
        rw [selected] at absent
        contradiction
  obtain ⟨candidate, found⟩ := found
  have tested := List.find?_some found
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at tested
  have candidatePrefix := List.isPrefixOf_iff_prefix.mp tested.2
  have same : candidate = symbol := by
    rcases Nat.le_total (codeOf lens candidate).length (codeOf lens symbol).length with order | order
    · exact Proofs.prefixFree acceptable.1 acceptable.2.1 tested.1 nonzero
        (List.isPrefixOf_iff_prefix.mpr
          (List.prefix_of_prefix_length_le candidatePrefix symbolPrefix order))
    · exact (Proofs.prefixFree acceptable.1 acceptable.2.1 nonzero tested.1
        (List.isPrefixOf_iff_prefix.mpr
          (List.prefix_of_prefix_length_le symbolPrefix candidatePrefix order))).symm
  subst candidate
  change decodeSym lens inp = _
  unfold decodeSym
  rw [found]
  have length : (codeOf lens symbol).length = lens.getD symbol 0 := by
    simp only [codeOf, Proofs.natToBitsMSB_length]
  dsimp only [inp]
  rw [← length, List.drop_left]

#print axioms allocation_order_nodup
#print axioms allocation_index_injective
#print axioms allocated_word_code
#print axioms decode_canonical_word

end ZlibF.Math.InflateDecode
