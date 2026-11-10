import ZlibF.Math.DeflateRankedLengths
namespace Zlib.Trees.HuffmanAbstract
set_option autoImplicit false
/-- The rank search characterization holds at any length limit. -/
theorem lenOfRank_eq_limit (limit : Nat) (c : Nat → Nat) (r ell : Nat)
    (bound : ell ≤ limit) (below : ∀ j, j < ell → cumC c j < r)
    (found : r ≤ cumC c ell) : lenOfRank limit c r = ell := by
  have spec := lenSearch_spec c r limit 0
  have le : lenOfRank limit c r ≤ ell := by
    apply Nat.le_of_not_lt
    intro opposite
    have no := spec.2.2.1 ell (by omega) opposite
    omega
  apply Nat.le_antisymm le
  apply Nat.le_of_not_lt
  intro opposite
  have yes := spec.2.2.2 (by
    simp only [Nat.zero_add]
    exact Nat.le_trans found (cumC_mono c bound))
  change r ≤ cumC c (lenOfRank limit c r) at yes
  have no := below (lenOfRank limit c r) opposite
  omega

/-- A bounded sorted length sequence with a complete histogram is the
actual rank-search result at that same limit, including maximum seven. -/
theorem lenOfRank_of_sorted_limit (limit N : Nat) (L c' : Nat → Nat)
    (hmono : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → L y ≤ L r) (hL : ∀ r, 1 ≤ r → r ≤ N → L r ≤ limit)
    (hcnt : ∀ j, j ≤ limit → c' j = countR (fun r => L r == j) N) :
    ∀ r, 1 ≤ r → r ≤ N → L r = lenOfRank limit c' r := by
  have hcum : ∀ j, j ≤ limit → cumC c' j = countR (fun r => decide (L r ≤ j)) N := by
    intro j hj
    rw [cumC_congr j (c' := fun j => countR (fun r => L r == j) N) fun i hi => hcnt i (by omega)]
    exact cumC_hist L N j
  have hpre : ∀ j r, 1 ≤ r → r ≤ N → (L r ≤ j ↔ r ≤ countR (fun r => decide (L r ≤ j)) N) := by
    intro j r h1 h2
    have := prefix_countR (fun r => decide (L r ≤ j)) N
      (fun y r' a b c hp => by simp at hp ⊢; have := hmono y r' a b c; omega) r h1 h2
    simpa using this
  intro r h1 h2
  symm
  refine lenOfRank_eq_limit limit c' r (L r) (hL r h1 h2) (fun j hj => ?_) ?_
  · rw [hcum j (by have := hL r h1 h2; omega)]
    have : ¬ (r ≤ countR (fun r => decide (L r ≤ j)) N) := fun hr => by
      have := (hpre j r h1 h2).2 hr; omega
    omega
  · rw [hcum _ (hL r h1 h2)]; exact (hpre (L r) r h1 h2).1 (Nat.le_refl _)

#print axioms lenOfRank_eq_limit
#print axioms lenOfRank_of_sorted_limit
end Zlib.Trees.HuffmanAbstract

namespace Zlib.Trees.Proofs.GB.LeafRank
set_option autoImplicit false
/-- Retained source heap ranks refine the generic limit-parametric search. -/
theorem value_eq_lenOfRank_limit (limit : Nat) {H f c : Nat → Nat} {hm J maxc : Nat}
    (ordered : ∀ q q', hm + 1 ≤ q → q ≤ q' → q' < 573 → H q ≤ maxc → H q' ≤ maxc → f (H q) ≤ f (H q'))
    (geometry : hm + 2 * J = 572)
    (lengths : ∀ r, 1 ≤ r → r ≤ count H hm J maxc → value H f hm J maxc r ≤ limit)
    (histogram : ∀ j, j ≤ limit → c j = blP H hm maxc f (2 * J) j) :
    ∀ r, 1 ≤ r → r ≤ count H hm J maxc →
      value H f hm J maxc r = Zlib.Trees.HuffmanAbstract.lenOfRank limit c r := by
  exact Zlib.Trees.HuffmanAbstract.lenOfRank_of_sorted_limit limit
    (count H hm J maxc) (value H f hm J maxc) c
    (value_sorted ordered geometry) lengths
    (fun j bound => (histogram j bound).trans (value_counts H f hm J maxc j).symm)
#print axioms value_eq_lenOfRank_limit
end Zlib.Trees.Proofs.GB.LeafRank
