import ZlibF.Spec.InflateFastTableFlags
import ZlibF.Proof.«inftrees.c.decode.frame»

set_option autoImplicit false
namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec
open Zlib.Inftrees.Spec.FastTableFlags Zlib.Inftrees.Spec.DecodeSoundness

theorem leaf_classification_agrees : FastTableFlags.Goal.leaf_classification_agrees := by
  intro type entry kind compatible shape
  rcases kind with type | type
  · subst type
    have leaf := (shape.1 rfl).2
    simp only [FastLeafAccepted, LeafAccepted, ite_true, bne_iff_ne]
    have ofValid : entry.op &&& 64 = 0 →
        entry.op = 0 ∨ entry.op &&& 16 ≠ 0 := by
      intro valid
      rcases leaf with literal | length | invalid
      · exact Or.inl literal
      · exact Or.inr length.1
      · exact False.elim (invalid.2 valid)
    constructor
    · intro fast
      rcases fast with literal | length | ending
      · exact Or.inr (by rw [literal]; rfl)
      · exact Or.inr (compatible length)
      · exact Or.inl ending.2
    · intro slow
      rcases slow with ending | valid
      · by_cases invalid : entry.op &&& 64 = 0
        · rcases ofValid invalid with literal | length
          · exact Or.inl literal
          · exact Or.inr (Or.inl length)
        · exact Or.inr (Or.inr ⟨invalid, ending⟩)
      · rcases ofValid valid with literal | length
        · exact Or.inl literal
        · exact Or.inr (Or.inl length)
  · subst type
    have leaf := (shape.2 rfl).2
    simp only [FastLeafAccepted, LeafAccepted, show DISTS ≠ LENS by decide, ite_false]
    constructor
    · exact compatible
    · intro valid
      rcases leaf with length | invalid
      · exact length.1
      · exact False.elim (invalid.2 valid)

theorem fast_leaf_flags_of_prefix : FastTableFlags.Goal.fast_leaf_flags_of_prefix := by
  intro type before after offset root used kind extent compatible cells inp entry consumed enough query
  have preserved := decode_table_read_preserved type before after offset root used kind extent cells inp
  rw [preserved] at query
  exact compatible inp entry consumed enough query

#print axioms leaf_classification_agrees
#print axioms fast_leaf_flags_of_prefix
end Zlib.Inftrees.Proofs
