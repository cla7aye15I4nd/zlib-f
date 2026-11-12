import ZlibF.Math.HuffmanReference
import ZlibF.Math.DeflateHuffmanDepth

/-!
# deflate.c: the tree `build_tree` builds is optimal against any complete reference code (H1)

The heap layout `PShape` of `build_tree`, with parent weights equal to the sum of the children
(`sums`) and nondecreasing removal weights (`ordered`), is a `SibTree`. Hence the cost of the used
symbols at their true depths (`Clamped … 1000`, before `gen_bitlen` limits the lengths) is at most
their cost under every complete code. This is H1 of the TinyOverlay header bound; the reference
used there is `κ0`. The premises `sums` and `ordered` are the ones `ws_gen_bitlen_fib_push` takes,
and the source constructor establishes them (`ws_build_tree_fib_plus_origins`).
-/

namespace Zlib.Trees.Proofs.GB
open ZlibF.Math.HuffmanReference
set_option autoImplicit false

section
variable {H : Nat → Nat} {hm J elems maxc : Nat}

/-- The heap tail read as a removal sequence (`nd p = heap[572 - p]`) has the sibling property. -/
theorem PShape.sibTree (S : PShape H hm J elems maxc) (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q')) :
    SibTree (fun p => H (572 - p)) w J elems where
  J1 := S.J1
  inj := by
    intro p p' hp hp' e
    have := S.hm_eq
    have := S.inj (572 - p) (572 - p') (by omega) (by omega) (by omega) (by omega) e
    omega
  kind := by
    intro p hp
    have := S.hm_eq
    show H (572 - p) < elems + J
    rcases S.kind (572 - p) (by omega) (by omega) with h | h
    · have := S.maxc_lt; omega
    · exact h.2
  root := by
    have := S.hm_eq
    show H (572 - 2 * J) = _
    rw [show 572 - 2 * J = hm by omega]
    exact S.root
  appears := by
    intro a ha
    have := S.hm_eq
    obtain ⟨q, h1, h2, e⟩ := S.appears a ha
    refine ⟨572 - q, by omega, by omega, ?_⟩
    show H (572 - (572 - q)) = _
    rw [show 572 - (572 - q) = q by omega]
    exact e
  sums := by
    intro a ha
    have := S.hm_eq
    show w (elems + a) = w (H (572 - 2 * a)) + w (H (572 - (2 * a + 1)))
    rw [show 572 - (2 * a + 1) = 571 - 2 * a by omega]
    exact sums a ha
  ordered := by
    intro p p' hpp hp'
    have := S.hm_eq
    exact ordered (572 - p) (572 - p') (by omega) (by omega) (by omega)

/-- A leaf sum over the removal positions is the leaf sum over the heap positions. -/
theorem PShape.removal_leaf_sum (S : PShape H hm J elems maxc) (F : Nat → Nat) :
    rs (fun p => if H (572 - p) < elems then F (H (572 - p)) else 0) (2 * J + 1) =
      rs (fun i => if H (hm + 1 + i) ≤ maxc then F (H (hm + 1 + i)) else 0) (2 * J) := by
  have hm_eq := S.hm_eq
  have lt := S.maxc_lt
  rw [rs_succ]
  have rootTerm : (if H (572 - 2 * J) < elems then F (H (572 - 2 * J)) else 0) = 0 := by
    rw [show 572 - 2 * J = hm by omega, S.root]
    exact ite_eq_right (by have := S.J1; omega)
  rw [rootTerm, Nat.add_zero]
  rw [← rs_perm (fun i => 2 * J - 1 - i) (fun p => if H (572 - p) < elems then F (H (572 - p)) else 0) (2 * J)
    (fun i hi => by try dsimp only
                    omega)
    (fun i j hi hj e => by try dsimp only at e
                           omega)]
  apply rs_congr
  intro i hi
  show (if H (572 - (2 * J - 1 - i)) < elems then F (H (572 - (2 * J - 1 - i))) else 0) = _
  rw [show 572 - (2 * J - 1 - i) = hm + 1 + i by omega]
  have leaf : H (hm + 1 + i) < elems ↔ H (hm + 1 + i) ≤ maxc := by
    rcases S.kind (hm + 1 + i) (by omega) (by omega) with h | h
    · constructor <;> intro _ <;> omega
    · constructor <;> intro _ <;> omega
  by_cases c : H (hm + 1 + i) ≤ maxc
  · rw [ite_eq_left (leaf.mpr c), ite_eq_left c]
  · rw [ite_eq_right (fun h => c (leaf.mp h)), ite_eq_right c]

/-- **H1 on the heap tree.** The used symbols (`T`) cost at most as much at their true depths as
under any complete code `ℓ` (`Σ_T 2^(K-ℓ) = 2^K`, `ℓ ≤ K` on `T`). -/
theorem PShape.depth_cost_le_complete (S : PShape H hm J elems maxc) {dl : Nat → Nat}
    (C : Clamped H hm J elems 1000 dl) (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (T : Nat → Prop) [DecidablePred T] (hT : ∀ v ≤ maxc, T v ↔ ∃ q, hm < q ∧ q < 573 ∧ H q = v)
    (K : Nat) (ℓ : Nat → Nat) (bound : ∀ v ≤ maxc, T v → ℓ v ≤ K)
    (kraft : rs (fun v => if T v then 2 ^ (K - ℓ v) else 0) (maxc + 1) = 2 ^ K) :
    rs (fun v => if T v then w v * dl v else 0) (maxc + 1) ≤
      rs (fun v => if T v then w v * ℓ v else 0) (maxc + 1) := by
  have hm_eq := S.hm_eq
  have lt := S.maxc_lt
  have sib := S.sibTree w sums ordered
  have hroot : dl (elems + J - 1) = 0 := by rw [← S.root]; exact C.root
  have hchild : ∀ a < J, dl ((fun p => H (572 - p)) (2 * a)) = dl (elems + a) + 1 ∧
      dl ((fun p => H (572 - p)) (2 * a + 1)) = dl (elems + a) + 1 := by
    intro a ha
    obtain ⟨q, h1, h2, e⟩ := S.appears a ha
    have c1 := dl_child S C h1 (by omega) e (c := 572 - 2 * a) (Or.inl rfl) (by omega) (by omega)
    have c2 := dl_child S C h1 (by omega) e (c := 571 - 2 * a) (Or.inr rfl) (by omega) (by omega)
    rw [e] at c1 c2
    refine ⟨c1, ?_⟩
    show dl (H (572 - (2 * a + 1))) = _
    rw [show 572 - (2 * a + 1) = 571 - 2 * a by omega]
    exact c2
  have main := sib.depth_le_complete dl hroot hchild K (fun p => ℓ (H (572 - p)))
    (by
      intro p hp leaf
      show ℓ (H (572 - p)) ≤ K
      have pos : 572 - p ≠ hm := by
        intro e
        rw [e, S.root] at leaf
        have := S.J1
        omega
      have mx : H (572 - p) ≤ maxc := by
        rcases S.kind (572 - p) (by omega) (by omega) with h | h
        · exact h
        · omega
      exact bound _ mx ((hT _ mx).mpr ⟨572 - p, by omega, by omega, rfl⟩))
    (by
      exact ((S.removal_leaf_sum (fun v => 2 ^ (K - ℓ v))).trans
        (S.leaf_sum T hT (fun v => 2 ^ (K - ℓ v)))).trans kraft)
  have eL := (S.removal_leaf_sum (fun v => w v * dl v)).trans (S.leaf_sum T hT (fun v => w v * dl v))
  have eR := (S.removal_leaf_sum (fun v => w v * ℓ v)).trans (S.leaf_sum T hT (fun v => w v * ℓ v))
  exact Nat.le_trans (Nat.le_of_eq eL.symm) (Nat.le_trans main (Nat.le_of_eq eR))

end

end Zlib.Trees.Proofs.GB
