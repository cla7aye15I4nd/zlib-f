import ZlibF.Math.HuffmanRank
import ZlibF.Math.HuffmanFib

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# `FibPush` after `gen_bitlen`'s overflow repair (the reference overlay analysis §7.2–7.3)

On count profiles `c` (levels `0 .. 15`, `c 0 = 0`), with Kraft excess `M` (that is,
`Σ c j 2^(15−j) = 2^15 + M`), `N = Σ c ≤ 2^15` and `c 15 ≥ M`:

* `push_cost`: rank `r` moves from length `d = lenOfRank c r` to `l = lenOfRank c' r`,
  where `c' = repairIter 15 M c`. The total cost `Σ_r pcost d l` is at most `M`. Here
  `pcost` is 0 (no push), 1 (one level), or `2^(14−d) + 1` (two levels or more). This is
  the budget argument of §7.3, by induction on `M`: deepest units are expanded first
  (`exp_full`), then one partial expansion (`exp_partial`).
* `rank_bound` (Lemma 7): with weights nonincreasing by rank and the Lemma 2 bound
  `w·F(δ+1) ≤ W` per leaf, `w_r · F(d(r)+1) ≤ W`.
* `fibPush_rank`: the two together give `FibPushR`. This covers the overflow case `M ≥ 1`.
  `fibPush_of_fibPlus` covers the case without overflow, where `gen_bitlen` keeps `l = δ`.
-/

namespace Zlib.Trees.HuffmanAbstract

/-- Cost of moving a rank from length `d` to length `l`. -/
def pcost (d l : Nat) : Nat := if l ≤ d then 0 else if l = d + 1 then 1 else 2 ^ (14 - d) + 1

theorem pcost_self (d : Nat) : pcost d d = 0 := by simp [pcost]

theorem pcost_15 {l : Nat} (h : l ≤ 15) : pcost 15 l = 0 := by simp [pcost, h]

theorem pcost_le_kappa (d l : Nat) : pcost d l ≤ 2 ^ (14 - d) + 1 := by
  unfold pcost
  generalize 2 ^ (14 - d) = P
  repeat' split
  all_goals omega

theorem pcost_le_T (s l : Nat) (hs : s ≤ 14) (hl : l ≤ 15) : pcost s l ≤ 2 ^ (15 - s) - 1 := by
  rcases Nat.lt_or_ge s 14 with h | h
  · have hP := two_pow_split s (by omega)
    have : 2 ≤ 2 ^ (14 - s) := by
      rw [show 14 - s = (13 - s) + 1 by omega, Nat.pow_succ]; have := @Nat.one_le_two_pow (13 - s); omega
    have := pcost_le_kappa s l; omega
  · have : s = 14 := by omega
    subst this; unfold pcost
    generalize 2 ^ (14 - 14) = P
    repeat' split
    all_goals omega

/-! ## Deepest nonempty level -/

theorem deepest_spec (c : Nat → Nat) : ∀ b,
    (c (deepest c b) ≠ 0 ∧ deepest c b ≤ b ∧ ∀ j, deepest c b < j → j ≤ b → c j = 0) ∨
      (deepest c b = 0 ∧ ∀ j, 1 ≤ j → j ≤ b → c j = 0)
  | 0 => by
    by_cases h : c 0 = 0
    · right; exact ⟨rfl, fun j h1 h2 => by omega⟩
    · left; exact ⟨h, Nat.le_refl 0, fun j h1 h2 => by change 0 < j at h1; omega⟩
  | b + 1 => by
    simp only [deepest]
    by_cases h : c (b + 1) ≠ 0
    · rw [if_pos h]; left; exact ⟨h, Nat.le_refl _, fun j h1 h2 => by omega⟩
    · rw [if_neg h]
      have h' : c (b + 1) = 0 := by omega
      rcases deepest_spec c b with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · left; refine ⟨h1, by omega, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (b + 1) with hj | hj
        · exact h3 j hj1 (by omega)
        · have : j = b + 1 := by omega
          subst this; exact h'
      · right; refine ⟨h1, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (b + 1) with hj | hj
        · exact h2 j hj1 (by omega)
        · have : j = b + 1 := by omega
          subst this; exact h'

theorem exists_deepest (c : Nat → Nat) (hne : ∃ j, 1 ≤ j ∧ j ≤ 14 ∧ c j ≠ 0) :
    ∃ s, 1 ≤ s ∧ s ≤ 14 ∧ 1 ≤ c s ∧ ∀ j, s < j → j ≤ 14 → c j = 0 := by
  obtain ⟨j0, hj1, hj2, hj3⟩ := hne
  rcases deepest_spec c 14 with ⟨h1, h2, h3⟩ | ⟨_, h2⟩
  · refine ⟨deepest c 14, ?_, h2, by omega, h3⟩
    rcases Nat.eq_zero_or_pos (deepest c 14) with h0 | h0
    · exact absurd (h3 j0 (by omega) hj2) hj3
    · exact h0
  · exact absurd (h2 j0 hj1 hj2) hj3

theorem wsum_zero_upto (wt c : Nat → Nat) : ∀ j, (∀ i, i ≤ j → c i = 0) → wsum wt c j = 0
  | 0, h => by simp [wsum, h 0 (Nat.le_refl _)]
  | j + 1, h => by
    simp [wsum, h (j + 1) (Nat.le_refl _), wsum_zero_upto wt c j fun i hi => h i (by omega)]

/-! ## The budget -/

/-- Characterization of the ranks around the deepest unit `s`. Ranks below
`K = cumC c s` have length at most `s`. Rank `K` has length `s`. The ranks above have
length 15. -/
theorem len_K (c : Nat → Nat) (s : Nat) (hs1 : 1 ≤ s) (hs : s ≤ 15) (hcs : 1 ≤ c s) :
    lenOfRank 15 c (cumC c s) = s ∧ ∀ j, j < s → cumC c j + 1 ≤ cumC c s := by
  have hprev : cumC c s = cumC c (s - 1) + c s := by
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩; rfl
  have hb : ∀ j, j < s → cumC c j + 1 ≤ cumC c s := by
    intro j hj; have := cumC_mono c (show j ≤ s - 1 by omega); omega
  exact ⟨lenOfRank_eq c _ s hs (fun j hj => by have := hb j hj; omega) (Nat.le_refl _), hb⟩

/-- **The push budget (§7.3).** -/
theorem push_cost : ∀ (M : Nat) (c : Nat → Nat), c 0 = 0 → krS c 15 = 2 ^ 15 + M →
    cumC c 15 ≤ 2 ^ 15 → M ≤ c 15 →
    sumR (fun r => pcost (lenOfRank 15 c r) (lenOfRank 15 (repairIter 15 M c) r)) (cumC c 15) ≤ M := by
  intro M
  induction M using Nat.strongRecOn with
  | ind M ih =>
  intro c hc0 hkr hN h15
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    have e : repairIter 15 0 c = c := rfl
    rw [e]
    calc _ ≤ sumR (fun _ => 0) (cumC c 15) := sumR_le _ (fun r _ _ => by rw [pcost_self]; exact Nat.le_refl _)
      _ = 0 := sumR_zero _
  -- a nonempty level in `1 .. 14`
  have hne : ∃ j, 1 ≤ j ∧ j ≤ 14 ∧ c j ≠ 0 := by
    refine Classical.byContradiction fun hno => ?_
    have hz : ∀ i, i ≤ 14 → c i = 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact hc0
      · exact Classical.byContradiction fun h' => hno ⟨i, h, hi, h'⟩
    have hk : krS c 15 = c 15 := by
      show wsum (fun i => 2 ^ (15 - i)) c 14 + c 15 * 2 ^ (15 - 15) = c 15
      rw [wsum_zero_upto _ c 14 hz]; simp
    have : cumC c 15 = cumC c 14 + c 15 := rfl
    omega
  obtain ⟨s, hs1, hs14, hcs, hz⟩ := exists_deepest c hne
  have hP1 := two_pow_14_pos s
  generalize hK : cumC c s = K
  have ⟨hlK, hbK⟩ := len_K c s hs1 (by omega) hcs
  rw [hK] at hlK hbK
  have hflat : ∀ j, s ≤ j → j ≤ 14 → cumC c j = K := by
    intro j h1 h2; rw [← hK]; exact cumC_flat c s j h1 fun i hi1 hi2 => hz i hi1 (by omega)
  have hN15 : cumC c 15 = cumC c 14 + c 15 := rfl
  have h14 : cumC c 14 = K := hflat 14 hs14 (Nat.le_refl _)
  -- ranks above `K` have length 15
  have hbig : ∀ r, K < r → r ≤ cumC c 15 → lenOfRank 15 c r = 15 := by
    intro r h1 h2
    refine lenOfRank_eq c r 15 (Nat.le_refl _) (fun j hj => ?_) h2
    have := cumC_mono c (show j ≤ 14 by omega); omega
  -- ranks below `K` keep their length under any profile `c'` that agrees below `s` and
  -- has `cumC c' s = K - 1`
  have hlow : ∀ (c' : Nat → Nat), (∀ j, j < s → cumC c' j = cumC c j) → cumC c' s + 1 = K →
      ∀ r, 1 ≤ r → r < K → lenOfRank 15 c' r = lenOfRank 15 c r := by
    intro c' hag hs' r hr1 hr2
    have hr15 : r ≤ cumC c 15 := by have := cumC_mono c (show s ≤ 15 by omega); omega
    have hℓs : lenOfRank 15 c r ≤ s := lenOfRank_le_of c r s (by omega) (by omega)
    refine lenOfRank_eq c' r _ (lenOfRank_le c r) (fun j hj => ?_) ?_
    · rw [hag j (by omega)]; exact lenOfRank_below c r j hj
    · rcases Nat.lt_or_ge (lenOfRank 15 c r) s with h | h
      · rw [hag _ h]; exact lenOfRank_found c r hr15
      · have : lenOfRank 15 c r = s := by omega
        rw [this]; omega
  rcases Nat.lt_or_ge M (2 ^ (15 - s) - 1) with hlt | hge
  · -- partial expansion: only rank `K` moves
    have hs13 : s ≤ 13 := by
      rcases Nat.lt_or_ge s 14 with h | h
      · omega
      · have : s = 14 := by omega
        subst this; simp at hlt; omega
    obtain ⟨hp1, hp2, hp3⟩ := exp_partial (14 - s) s (by omega) c M hz hcs hMpos hlt h15
    generalize hc' : repairIter 15 M c = c' at hp1 hp2 hp3
    have hag : ∀ j, j < s → cumC c' j = cumC c j := fun j hj =>
      cumC_congr j fun i hi => hp1 i (by omega)
    have hs' : cumC c' s + 1 = K := by
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      have e1 : cumC c' (k + 1) = cumC c' k + c' (k + 1) := rfl
      have e2 : cumC c (k + 1) = cumC c k + c (k + 1) := rfl
      rw [e1, hag k (by omega), hp2]; rw [← hK, e2]; omega
    have hpt : ∀ r, 1 ≤ r → r ≤ cumC c 15 →
        pcost (lenOfRank 15 c r) (lenOfRank 15 c' r) ≤ (if r = K then M else 0) := by
      intro r hr1 hr2
      rcases Nat.lt_trichotomy r K with h | h | h
      · rw [hlow c' hag hs' r hr1 h, pcost_self]; exact Nat.zero_le _
      · rw [h, if_pos rfl, hlK]
        rcases Nat.lt_or_ge (2 ^ (14 - s)) M with hM | hM
        · have := pcost_le_kappa s (lenOfRank 15 c' K); omega
        · have hc1 := hp3 hM
          have : lenOfRank 15 c' K ≤ s + 1 := by
            refine lenOfRank_le_of c' _ (s + 1) (by omega) ?_
            have : cumC c' (s + 1) = cumC c' s + c' (s + 1) := rfl
            omega
          unfold pcost; split
          · exact Nat.zero_le _
          · rw [if_pos (by omega)]; omega
      · rw [hbig r h hr2, pcost_15 (lenOfRank_le c' r)]; exact Nat.zero_le _
    calc _ ≤ sumR (fun r => if r = K then M else 0) (cumC c 15) := sumR_le _ hpt
      _ ≤ M := sumR_single K M _
  · -- full expansion of one unit at `s`, then induction
    have hT := exp_full (14 - s) s (by omega) c hz hcs (by omega)
    have hsplit : M = (2 ^ (15 - s) - 1) + (M - (2 ^ (15 - s) - 1)) := by omega
    have hshift := wsum_shift (f := c) (g := fx c s) (a := 15) (b := s)
      (h := by intro i; simp only [fx]; (repeat' split) <;> (try subst_vars) <;> omega)
    have hcum : ∀ j, cumC c j + (if 15 ≤ j then 1 else 0) = cumC (fx c s) j + (if s ≤ j then 1 else 0) := by
      intro j; rw [cumC_eq_wsum, cumC_eq_wsum]; exact hshift (fun _ => 1) j
    have hkr1 := hshift (fun i => 2 ^ (15 - i)) 15
    simp only [Nat.le_refl, if_true, show s ≤ 15 by omega, Nat.sub_self, Nat.pow_zero] at hkr1
    have hkr1' : krS (fx c s) 15 + 2 ^ (15 - s) = krS c 15 + 1 := by simp only [krS]; omega
    have hN1 : cumC (fx c s) 15 = cumC c 15 := by
      have := hcum 15; simp only [Nat.le_refl, if_true, show s ≤ 15 by omega] at this; omega
    have hP := Nat.one_le_two_pow (n := 15 - s)
    have hP2 : 2 ≤ 2 ^ (15 - s) := by
      rw [show 15 - s = (14 - s) + 1 by omega, Nat.pow_succ]; omega
    have ih' := ih (M - (2 ^ (15 - s) - 1)) (by omega) (fx c s)
      (by simp only [fx]; rw [if_neg (by omega), if_neg (by omega)]; exact hc0)
      (by omega) (by omega) (by simp only [fx]; rw [if_neg (by omega)]; simp; omega)
    rw [hN1] at ih'
    have hfin : repairIter 15 M c = repairIter 15 (M - (2 ^ (15 - s) - 1)) (fx c s) := by
      conv => lhs; rw [hsplit]
      rw [repairIter_add, hT]
    rw [hfin]
    generalize hx : repairIter 15 (M - (2 ^ (15 - s) - 1)) (fx c s) = cf at ih'
    have hag : ∀ j, j < s → cumC (fx c s) j = cumC c j := by
      intro j hj; have := hcum j; rw [if_neg (by omega), if_neg (by omega)] at this; omega
    have hs' : cumC (fx c s) s + 1 = K := by
      have := hcum s; rw [if_neg (by omega), if_pos (Nat.le_refl _)] at this; omega
    have hpt : ∀ r, 1 ≤ r → r ≤ cumC c 15 →
        pcost (lenOfRank 15 c r) (lenOfRank 15 cf r) ≤
          pcost (lenOfRank 15 (fx c s) r) (lenOfRank 15 cf r) + (if r = K then 2 ^ (15 - s) - 1 else 0) := by
      intro r hr1 hr2
      rcases Nat.lt_trichotomy r K with h | h | h
      · rw [hlow (fx c s) hag hs' r hr1 h]; omega
      · rw [h, if_pos rfl, hlK]
        have := pcost_le_T s (lenOfRank 15 cf K) hs14 (lenOfRank_le cf _); omega
      · rw [hbig r h hr2, pcost_15 (lenOfRank_le cf r)]; exact Nat.zero_le _
    calc _ ≤ sumR (fun r => pcost (lenOfRank 15 (fx c s) r) (lenOfRank 15 cf r) +
              (if r = K then 2 ^ (15 - s) - 1 else 0)) (cumC c 15) := sumR_le _ hpt
      _ = _ := sumR_add _ _ _
      _ ≤ (M - (2 ^ (15 - s) - 1)) + (2 ^ (15 - s) - 1) :=
          Nat.add_le_add ih' (sumR_single K _ _)
      _ = M := by omega

/-- Pushed ranks have their original length at most 14, so there are at most
`cumC c 14` of them. -/
theorem push_count (c : Nat → Nat) (l : Nat → Nat) (hl : ∀ r, l r ≤ 15) :
    sumR (fun r => if pcost (lenOfRank 15 c r) (l r) = 0 then 0 else 1) (cumC c 15) ≤ cumC c 14 := by
  refine Nat.le_trans (sumR_le _ fun r hr1 hr2 => ?_) (countR_le_bound (cumC c 14) _)
  show (if pcost (lenOfRank 15 c r) (l r) = 0 then 0 else 1) ≤ (if r ≤ cumC c 14 then 1 else 0)
  by_cases h : pcost (lenOfRank 15 c r) (l r) = 0
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]
    have hlt : lenOfRank 15 c r < l r := by
      unfold pcost at h; split at h
      · exact absurd rfl h
      · omega
    have := hl r
    have h1 := lenOfRank_found c r hr2
    have h2 := cumC_mono c (show lenOfRank 15 c r ≤ 14 by omega)
    rw [if_pos (by omega)]; exact Nat.le_refl _

end Zlib.Trees.HuffmanAbstract
