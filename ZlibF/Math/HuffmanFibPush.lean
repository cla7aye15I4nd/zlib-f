import ZlibF.Math.HuffmanPush

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# `FibPush` for the abstract `build_tree` + `gen_bitlen` (the reference overlay analysis §7.3)

The leaves are indexed by rank `r = 1 .. N`, where rank 1 is the leaf removed last. `w r`
is the weight of rank `r` and `δ r` its Huffman depth. `histR δ N` is the capped depth
histogram, i.e. the `bl_count` after the first pass of `gen_bitlen`.

* `rank_bound` (Lemma 7): `w r · F(d(r) + 1) ≤ W` with `d(r) = lenOfRank 15 (histR δ N) r`.
* `fibPush_rank`: with an overflow (`M ≥ 1` repair moves), the lengths
  `lenOfRank 15 (repairIter 15 M (histR δ N)) r` that `gen_bitlen` assigns satisfy
  `FibPushR`.
* `fibPush_of_fibPlus`: without an overflow (`gen_bitlen` keeps `l = δ`), `FibPlus`
  gives `FibPushR` with every rank in class 0.
* `lenOfRank_of_sorted`: lengths that are nondecreasing in rank and have the counts `c'`
  are `lenOfRank 15 c'`. This is the form in which the C reassignment loop delivers them.
-/

namespace Zlib.Trees.HuffmanAbstract

/-- The capped depth histogram: `histR δ N j = #{1 ≤ r ≤ N : min (δ r) 15 = j}`. -/
def histR (δ : Nat → Nat) (N j : Nat) : Nat := countR (fun r => min (δ r) 15 == j) N

theorem sumR_congr {f g : Nat → Nat} (n : Nat) (h : ∀ r, 1 ≤ r → r ≤ n → f r = g r) : sumR f n = sumR g n :=
  Nat.le_antisymm (sumR_le n fun r h1 h2 => Nat.le_of_eq (h r h1 h2))
    (sumR_le n fun r h1 h2 => Nat.le_of_eq (h r h1 h2).symm)

theorem countR_all (p : Nat → Bool) : ∀ n, (∀ r, 1 ≤ r → r ≤ n → p r = true) → countR p n = n
  | 0, _ => rfl
  | n + 1, h => by
    have := countR_all p n fun r h1 h2 => h r h1 (by omega)
    simp only [countR, sumR] at this ⊢; rw [this, h (n + 1) (by omega) (Nat.le_refl _)]; rfl

theorem countR_none (p : Nat → Bool) (n : Nat) (h : ∀ r, 1 ≤ r → r ≤ n → p r = false) : countR p n = 0 := by
  unfold countR
  rw [sumR_congr n (g := fun _ => 0) fun r h1 h2 => by rw [h r h1 h2]; rfl]
  exact sumR_zero n

/-- Cumulative counts of a histogram are counts of `≤`. -/
theorem cumC_hist (m : Nat → Nat) (N : Nat) : ∀ j,
    cumC (fun j => countR (fun r => m r == j) N) j = countR (fun r => decide (m r ≤ j)) N
  | 0 => by
    show countR _ N = countR _ N
    unfold countR; exact sumR_congr N fun r _ _ => by
      by_cases h : m r = 0 <;> simp [h]
  | j + 1 => by
    show cumC _ j + countR _ N = _
    rw [cumC_hist m N j]
    unfold countR
    rw [← sumR_add]
    exact sumR_congr N fun r _ _ => by
      by_cases h1 : m r ≤ j
      · simp [h1, show m r ≤ j + 1 by omega, show m r ≠ j + 1 by omega]
      · by_cases h2 : m r = j + 1
        · simp [h2]
        · simp [h1, h2, show ¬ m r ≤ j + 1 by omega]

theorem cumC_histR (δ : Nat → Nat) (N j : Nat) :
    cumC (histR δ N) j = countR (fun r => decide (min (δ r) 15 ≤ j)) N :=
  cumC_hist (fun r => min (δ r) 15) N j

theorem cumC_histR_15 (δ : Nat → Nat) (N : Nat) : cumC (histR δ N) 15 = N := by
  rw [cumC_histR]; exact countR_all _ N fun r _ _ => by simp; omega

theorem histR_zero (δ : Nat → Nat) (N : Nat) (hδ : ∀ r, 1 ≤ r → r ≤ N → 1 ≤ δ r) : histR δ N 0 = 0 :=
  countR_none _ N fun r h1 h2 => by have := hδ r h1 h2; simp; omega

/-- **Lemma 7 (rank bound).** Suppose weights are nonincreasing in rank and every leaf has
`w·F(δ+1) ≤ W`. Then the rank `r` has `w r · F(d(r)+1) ≤ W`, where `d(r)` is the length that
rank `r` would get by rank from the capped depth histogram. -/
theorem rank_bound (N W : Nat) (w δ : Nat → Nat)
    (hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y)
    (hL2 : ∀ y, 1 ≤ y → y ≤ N → w y * fib (δ y + 1) ≤ W) :
    ∀ r, 1 ≤ r → r ≤ N → w r * fib (lenOfRank 15 (histR δ N) r + 1) ≤ W := by
  intro r hr1 hr2
  generalize hd : lenOfRank 15 (histR δ N) r = d
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    have := hL2 r hr1 hr2
    have : fib 1 ≤ fib (δ r + 1) := fib_mono (by omega)
    have : w r * fib 1 ≤ w r * fib (δ r + 1) := Nat.mul_le_mul_left _ this
    show w r * fib 1 ≤ W
    omega
  · have hbel := lenOfRank_below (histR δ N) r (d - 1) (by omega)
    rw [cumC_histR] at hbel
    have hmono := countR_mono (fun r => decide (min (δ r) 15 ≤ d - 1)) hr2
    obtain ⟨y, hy1, hy2, hy3⟩ := exists_not_of_countR_lt (fun r => decide (min (δ r) 15 ≤ d - 1)) r (by omega)
    have hy3' : ¬ (min (δ y) 15 ≤ d - 1) := by simpa using hy3
    have hd15 : d ≤ 15 := by rw [← hd]; exact lenOfRank_le _ _
    have hδy : d ≤ δ y := by omega
    have h1 : w r * fib (d + 1) ≤ w y * fib (δ y + 1) :=
      Nat.mul_le_mul (hw y r hy1 hy2 hr2) (fib_mono (by omega))
    exact Nat.le_trans h1 (hL2 y hy1 (by omega))

theorem pcost_cases (d l : Nat) :
    (pcost d l = 0 ∧ l ≤ d) ∨ (pcost d l = 1 ∧ l = d + 1) ∨ (pcost d l = 2 ^ (14 - d) + 1 ∧ d + 2 ≤ l) := by
  unfold pcost
  by_cases h1 : l ≤ d
  · left; simp [h1]
  · by_cases h2 : l = d + 1
    · right; left; simp [h2]
    · right; right; simp [h1, h2]; omega

/-- **`FibPush` after an overflow (§7.3).** The hypotheses, as `build_tree` and
`gen_bitlen` provide them:
* `hδ`: every Huffman depth is at least 1 (there are `N ≥ 2` leaves);
* `hw`: weights are nonincreasing in rank (Lemma 1(b): removal order is nondecreasing in
  `Freq`);
* `hL2`: Lemma 2 for each leaf (`fibChain_bound` or `fibPlus_of_merges`);
* `hN`: `N ≤ 2^15`;
* `hkr`: the capped Kraft sum is `2^15 + M`, where `M = overflow / 2` (Lemma 3);
* `h15`: `bl_count[15] ≥ M + 1` (Lemma 3; `kraft_clamped` in `GenBitlenMath`).

The lengths are those of the reassignment by rank after `M` repair moves. -/
theorem fibPush_rank (N W M : Nat) (w δ : Nat → Nat)
    (hδ : ∀ r, 1 ≤ r → r ≤ N → 1 ≤ δ r)
    (hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y)
    (hL2 : ∀ y, 1 ≤ y → y ≤ N → w y * fib (δ y + 1) ≤ W)
    (hN : N ≤ 2 ^ 15) (hkr : krS (histR δ N) 15 = 2 ^ 15 + M) (h15 : M + 1 ≤ histR δ N 15) :
    FibPushR N W w (fun r => lenOfRank 15 (repairIter 15 M (histR δ N)) r) := by
  generalize hc : histR δ N = c at hkr h15
  have hc0 : c 0 = 0 := by rw [← hc]; exact histR_zero δ N hδ
  have hcN : cumC c 15 = N := by rw [← hc]; exact cumC_histR_15 δ N
  have hcost := push_cost M c hc0 hkr (by omega) (by omega)
  have hcnt := push_count c (fun r => lenOfRank 15 (repairIter 15 M c) r) fun r => lenOfRank_le _ _
  rw [hcN] at hcost hcnt
  have h14 : cumC c 15 = cumC c 14 + c 15 := rfl
  have hrb := rank_bound N W w δ hw hL2
  rw [hc] at hrb
  refine ⟨fun r => if pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) = 0 then 0 else if pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) = 1 then 1 else 2, fun r => lenOfRank 15 c r, ?_, ?_⟩
  · intro r hr1 hr2
    dsimp only
    have hb := hrb r hr1 hr2
    have hl15 : lenOfRank 15 (repairIter 15 M c) r ≤ 15 := lenOfRank_le _ _
    rcases pcost_cases (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) with ⟨hp, hle⟩ | ⟨hp, heq⟩ | ⟨hp, hge⟩
    · left; refine ⟨by simp [hp], ?_⟩
      have hf : fib (lenOfRank 15 (repairIter 15 M c) r + 1) ≤ fib (lenOfRank 15 c r + 1) :=
        fib_mono (by omega)
      exact Nat.le_trans (Nat.mul_le_mul_left _ hf) hb
    · right; left; refine ⟨by simp [hp], ?_⟩
      rw [heq]; exact hb
    · right; right
      have hne0 : pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) ≠ 0 := by have := Nat.one_le_two_pow (n := 14 - lenOfRank 15 c r); omega
      have hne1 : pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) ≠ 1 := by
        have : 2 ≤ 2 ^ (14 - lenOfRank 15 c r) := by
          rw [show 14 - lenOfRank 15 c r = (13 - lenOfRank 15 c r) + 1 by omega, Nat.pow_succ]
          have := Nat.one_le_two_pow (n := 13 - lenOfRank 15 c r); omega
        omega
      refine ⟨by simp [hne0, hne1], ?_, by omega, hb⟩
      -- the origin is at least 1: rank `r ≥ 1` is not at level 0
      refine Nat.pos_of_ne_zero fun h0 => ?_
      have := lenOfRank_found c r (by omega)
      rw [h0] at this
      have : cumC c 0 = c 0 := rfl
      omega
  · have hpt : ∀ r, 1 ≤ r → r ≤ N →
        pushCostA (if pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) = 0 then 0 else if pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) = 1 then 1 else 2) (lenOfRank 15 c r) =
          pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) + (if pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) = 0 then 0 else 1) := by
      intro r _ _
      rcases pcost_cases (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, hge⟩
      · simp [hp, pushCostA]
      · simp [hp, pushCostA]
      · have hne0 : pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) ≠ 0 := by have := Nat.one_le_two_pow (n := 14 - lenOfRank 15 c r); omega
        have := lenOfRank_le (repairIter 15 M c) r
        have h2 : 2 ≤ 2 ^ (14 - lenOfRank 15 c r) := by
          rw [show 14 - lenOfRank 15 c r = (13 - lenOfRank 15 c r) + 1 by omega, Nat.pow_succ]
          have := Nat.one_le_two_pow (n := 13 - lenOfRank 15 c r); omega
        have hne1 : pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r) ≠ 1 := by omega
        simp only [hne0, hne1, if_false, pushCostA, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide]
        omega
    dsimp only
    rw [sumR_congr N hpt, sumR_add]
    omega

/-- **No overflow.** If every rank has `w·F(l+1) ≤ W` (`FibPlus`, `l = δ`), then
`FibPushR` holds with every rank in class 0. -/
theorem fibPush_of_fibPlus (N W : Nat) (w l : Nat → Nat) (hN : 1 ≤ N)
    (h : ∀ r, 1 ≤ r → r ≤ N → w r * fib (l r + 1) ≤ W) : FibPushR N W w l := by
  refine ⟨fun _ => 0, fun _ => 0, fun r h1 h2 => Or.inl ⟨rfl, h r h1 h2⟩, ?_⟩
  have : sumR (fun r => pushCostA ((fun _ => 0) r) ((fun _ => 0) r)) N = 0 := by
    rw [sumR_congr N (g := fun _ => 0) fun r _ _ => by simp [pushCostA]]; exact sumR_zero N
  omega

/-- A downward-closed predicate on ranks `1 .. N` holds exactly on the first
`countR p N` ranks. -/
theorem prefix_countR (p : Nat → Bool) : ∀ N, (∀ y r, 1 ≤ y → y ≤ r → r ≤ N → p r = true → p y = true) →
    ∀ r, 1 ≤ r → r ≤ N → (p r = true ↔ r ≤ countR p N)
  | 0, _, r, h1, h2 => by omega
  | N + 1, hd, r, h1, h2 => by
    by_cases hN : p (N + 1) = true
    · have hall : countR p (N + 1) = N + 1 :=
        countR_all p (N + 1) fun y hy1 hy2 => hd y (N + 1) hy1 hy2 (Nat.le_refl _) hN
      rw [hall]; exact ⟨fun _ => h2, fun _ => hd r (N + 1) h1 h2 (Nat.le_refl _) hN⟩
    · have hc : countR p (N + 1) = countR p N := by
        simp only [countR, sumR]; simp [hN]
      rw [hc]
      rcases Nat.lt_or_ge r (N + 1) with hr | hr
      · exact prefix_countR p N (fun y r' a b c => hd y r' a b (by omega)) r h1 (by omega)
      · have : r = N + 1 := by omega
        subst this
        have := countR_le_n p N
        exact ⟨fun h => absurd h hN, fun h => by omega⟩

/-- **Sorted lengths are lengths by rank.** Lengths `L r ≤ 15`, nondecreasing in rank, with
`c' j` of them equal to `j` for every `j ≤ 15`, are `L r = lenOfRank 15 c' r`. -/
theorem lenOfRank_of_sorted (N : Nat) (L c' : Nat → Nat)
    (hmono : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → L y ≤ L r) (hL : ∀ r, 1 ≤ r → r ≤ N → L r ≤ 15)
    (hcnt : ∀ j, j ≤ 15 → c' j = countR (fun r => L r == j) N) :
    ∀ r, 1 ≤ r → r ≤ N → L r = lenOfRank 15 c' r := by
  have hcum : ∀ j, j ≤ 15 → cumC c' j = countR (fun r => decide (L r ≤ j)) N := by
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
  refine lenOfRank_eq c' r (L r) (hL r h1 h2) (fun j hj => ?_) ?_
  · rw [hcum j (by have := hL r h1 h2; omega)]
    have : ¬ (r ≤ countR (fun r => decide (L r ≤ j)) N) := fun hr => by
      have := (hpre j r h1 h2).2 hr; omega
    omega
  · rw [hcum _ (hL r h1 h2)]; exact (hpre (L r) r h1 h2).1 (Nat.le_refl _)

end Zlib.Trees.HuffmanAbstract
