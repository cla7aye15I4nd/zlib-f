import ZlibF.Math.HuffmanReference

/-!
# The root of a sibling tree weighs its leaves

For the removal sequence of `build_tree` (`SibTree`), the root weight is the sum of the leaf
weights: every merge replaces two live nodes by their parent, which weighs their sum.
-/

namespace ZlibF.Math.HuffmanReference
open Zlib.Trees.Proofs.GB
set_option autoImplicit false

section tree
variable {nd wN : Nat → Nat} {J elems : Nat}

/-- **Root weight.** The root weighs the sum of the leaf weights. -/
theorem SibTree.root_weight (S : SibTree nd wN J elems) :
    wN (elems + J - 1) = rs (fun p => if nd p < elems then wN (nd p) else 0) (2 * J + 1) := by
  have key : ∀ k, k ≤ J → wN (elems + J - 1) =
      rs (fun p => if stage nd elems (J - k) p then wN (nd p) else 0) (2 * J + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      rw [rs_succ]
      have before : rs (fun p => if stage nd elems J p then wN (nd p) else 0) (2 * J) = 0 := by
        apply rs_eq_zero
        intro p hp
        have off : stage nd elems J p = false := by
          simp only [stage, decide_eq_false_iff_not]; omega
        rw [off]; rfl
      have top : stage nd elems J (2 * J) = true := by
        simp only [stage, decide_eq_true_eq, S.root]
        have := S.J1
        omega
      rw [before]
      simp only [top, ite_true, S.root, Nat.zero_add]
    | succ k ih =>
      intro hk
      let a := J - (k + 1)
      have ha : a < J := by omega
      have succA : J - k = a + 1 := by omega
      obtain ⟨q, hq1, hq2, eq⟩ := S.appears a ha
      have next := S.stage_next ha hq2 eq
      have recur := ih (by omega)
      rw [succA] at recur
      have i0 : 2 * a < 2 * J + 1 := by omega
      have j0 : 2 * a + 1 < 2 * J + 1 := by omega
      have q0 : q < 2 * J + 1 := by omega
      have qi : q ≠ 2 * a := by omega
      have qj : q ≠ 2 * a + 1 := by omega
      have same : ∀ p < 2 * J + 1, p ≠ 2 * a → p ≠ 2 * a + 1 → p ≠ q →
          (if stage nd elems a p then wN (nd p) else 0) =
            (if stage nd elems (a + 1) p then wN (nd p) else 0) := by
        intro p hp pi pj pq
        have iff := next p hp
        by_cases ap : stage nd elems a p = true
        · rw [ite_eq_left ap, ite_eq_left (iff.mpr (Or.inl ⟨ap, pi, pj⟩))]
        · have ap' : stage nd elems (a + 1) p = false := by
            by_cases h : stage nd elems (a + 1) p = true
            · rcases iff.mp h with ⟨h1, _⟩ | h2
              · exact absurd h1 ap
              · exact absurd h2 pq
            · simpa using h
          simp only [Bool.not_eq_true] at ap
          rw [ap, ap']
      have three := rs_three i0 j0 q0 (by omega) (Ne.symm qi) (Ne.symm qj) same
      have s_i : stage nd elems a (2 * a) = true := by
        simp only [stage, decide_eq_true_eq]; exact ⟨Nat.le_refl _, S.child_below ha (by omega)⟩
      have s_j : stage nd elems a (2 * a + 1) = true := by
        simp only [stage, decide_eq_true_eq]; exact ⟨by omega, S.child_below ha (Nat.le_refl _)⟩
      have s_q : stage nd elems a q = false := by
        simp only [stage, eq, decide_eq_false_iff_not]; omega
      have t_i : stage nd elems (a + 1) (2 * a) = false := by
        simp only [stage, decide_eq_false_iff_not]; omega
      have t_j : stage nd elems (a + 1) (2 * a + 1) = false := by
        simp only [stage, decide_eq_false_iff_not]; omega
      have t_q : stage nd elems (a + 1) q = true := by
        simp only [stage, eq, decide_eq_true_eq]; omega
      simp only [s_i, s_j, s_q, t_i, t_j, t_q, ite_true, Bool.false_eq_true, ite_false, eq] at three
      rw [S.sums a ha] at three
      show wN (elems + J - 1) = rs (fun p => if stage nd elems a p then wN (nd p) else 0) (2 * J + 1)
      rw [recur]
      omega
  have top := key J (Nat.le_refl J)
  rw [top]
  apply rs_congr
  intro p _
  simp only [Nat.sub_self, stage, Nat.mul_zero, Nat.zero_le, true_and, Nat.add_zero, decide_eq_true_eq]

end tree

end ZlibF.Math.HuffmanReference
