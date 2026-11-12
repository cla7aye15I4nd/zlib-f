import ZlibF.Math.HuffmanFibPush

/-!
# The cost of `gen_bitlen`'s length repair, by rank (H2a, heap-free half)

Leaves are indexed by rank `r = 1 .. N` (rank 1 is removed last), with weights `w`
nonincreasing in rank and true Huffman depths `δ`. `histL L δ N` is the clamped depth histogram
that the first pass of `gen_bitlen` leaves for `max_length = L`, and the final lengths are
`lenOfRank 15 (repairIter L M (histL L δ N))`.

* `lenOfRank_repairStep`: one repair step lengthens only the rank `cumC c b` (`b` the level the
  step takes a leaf from), and that one by at most one level.
* `cost_repairIter`: hence the sorted cost grows by at most `repairExtra L w M c`, the sum of
  the weights of those ranks over the `M` steps.
* `sorted_cost_le`: the sorted pairing of a histogram with nonincreasing weights costs at most
  any other pairing with the same histogram (rearrangement).
* `repair_cost_le`: `Σ_r w r · len r ≤ Σ_r w r · δ r + repairExtra L w M (histL L δ N)`.

No step validity is assumed: the bound holds for every count vector.
-/

namespace Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- The clamped depth histogram for the length limit `L`. -/
def histL (L : Nat) (δ : Nat → Nat) (N j : Nat) : Nat := countR (fun r => min (δ r) L == j) N

/-- The weights of the ranks that the `M` repair steps lengthen. -/
def repairExtra (L : Nat) (w : Nat → Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | M + 1, c => w (cumC c (deepest c (L - 1))) + repairExtra L w M (repairStep L c)

theorem deepest_le_self (c : Nat → Nat) : ∀ b, deepest c b ≤ b
  | 0 => by simp [deepest]
  | b + 1 => by
    simp only [deepest]
    split
    · exact Nat.le_refl _
    · have := deepest_le_self c b; omega

/-- The counts after one repair step, in closed form (`b` the level the step takes from). -/
theorem repairStep_val (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b)
    (x : Nat) :
    repairStep L c x =
      if x = L then (if L = b + 1 then c L + 2 else c L) - 1
      else if x = b + 1 then c x + 2
      else if x = b then c x - 1
      else c x := by
  have hb := deepest_le_self c (L - 1)
  rw [hB] at hb
  simp only [repairStep, updC, hB]
  by_cases h1 : x = L
  · subst h1
    have h3 : x ≠ b := by omega
    by_cases h2 : x = b + 1
    · subst h2
      simp
    · simp [h2, h3]
  · by_cases h2 : x = b + 1
    · subst h2
      simp [h1]
    · by_cases h3 : x = b
      · subst h3; simp [h1]
      · simp [h1, h2, h3]

theorem repairStep_top (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b) :
    repairStep L c L = (if L = b + 1 then c L + 2 else c L) - 1 := by
  rw [repairStep_val L c hL b hB, ite_eq_left rfl]

theorem repairStep_up (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b)
    {x : Nat} (h1 : x ≠ L) (h2 : x = b + 1) : repairStep L c x = c x + 2 := by
  rw [repairStep_val L c hL b hB, ite_eq_right h1, ite_eq_left h2]

theorem repairStep_down (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b)
    {x : Nat} (h3 : x = b) : repairStep L c x = c x - 1 := by
  have hb := deepest_le_self c (L - 1)
  rw [repairStep_val L c hL b hB, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h3]

theorem repairStep_same (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b)
    {x : Nat} (h1 : x ≠ L) (h2 : x ≠ b + 1) (h3 : x ≠ b) : repairStep L c x = c x := by
  rw [repairStep_val L c hL b hB, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- Cumulative counts after one repair step. -/
theorem cumC_repairStep (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (b : Nat) (hB : deepest c (L - 1) = b) :
    ∀ j,
    (j < b → cumC (repairStep L c) j = cumC c j) ∧
    (j = b → cumC c j ≤ cumC (repairStep L c) j + 1 ∧ (c j = 0 → cumC c j ≤ cumC (repairStep L c) j)) ∧
    (b < j → j < L → cumC c j + 1 ≤ cumC (repairStep L c) j) ∧
    (L ≤ j → cumC c j ≤ cumC (repairStep L c) j)
  | 0 => by
    have hb := deepest_le_self c (L - 1)
    rw [hB] at hb
    have e1 : cumC c 0 = c 0 := rfl
    have e2 : cumC (repairStep L c) 0 = repairStep L c 0 := rfl
    by_cases z : 0 = b
    · have v := repairStep_down L c hL b hB z
      exact ⟨fun h => by omega, fun _ => ⟨by omega, fun _ => by omega⟩, fun h _ => by omega, fun h => by omega⟩
    · have v := repairStep_same L c hL b hB (x := 0) (by omega) (by omega) z
      exact ⟨fun _ => by omega, fun h => by omega, fun h _ => by omega, fun h => by omega⟩
  | j + 1 => by
    have hb := deepest_le_self c (L - 1)
    rw [hB] at hb
    obtain ⟨a1, a2, a3, a4⟩ := cumC_repairStep L c hL b hB j
    have e1 : cumC c (j + 1) = cumC c j + c (j + 1) := rfl
    have e2 : cumC (repairStep L c) (j + 1) = cumC (repairStep L c) j + repairStep L c (j + 1) := rfl
    by_cases hA : j + 1 = L
    · have v : repairStep L c (j + 1) = (if j + 1 = b + 1 then c (j + 1) + 2 else c (j + 1)) - 1 := by
        rw [hA]; exact repairStep_top L c hL b hB
      by_cases hJ : j = b
      · rw [ite_eq_left (by omega)] at v
        have := (a2 hJ).1
        exact ⟨fun h => by omega, fun h => by omega, fun _ h => by omega, fun _ => by omega⟩
      · rw [ite_eq_right (by omega)] at v
        have := a3 (by omega) (by omega)
        exact ⟨fun h => by omega, fun h => by omega, fun _ h => by omega, fun _ => by omega⟩
    · by_cases hJ : j = b
      · have v := repairStep_up L c hL b hB hA (by omega)
        have := (a2 hJ).1
        exact ⟨fun h => by omega, fun h => by omega, fun _ _ => by omega, fun h => by omega⟩
      · by_cases hC : j + 1 = b
        · have v := repairStep_down L c hL b hB hC
          have := a1 (by omega)
          exact ⟨fun h => by omega, fun _ => ⟨by omega, fun _ => by omega⟩, fun h _ => by omega,
            fun h => by omega⟩
        · have v := repairStep_same L c hL b hB hA (by omega) hC
          refine ⟨fun h => ?_, fun h => by omega, fun h h' => ?_, fun h => ?_⟩
          · have := a1 (by omega); omega
          · have := a3 (by omega) (by omega); omega
          · have := a4 (by omega); omega

theorem lenSearch_stop (c : Nat → Nat) (r : Nat) : ∀ fuel k,
    lenSearch c r k fuel < k + fuel → r ≤ cumC c (lenSearch c r k fuel)
  | 0, k => by simp [lenSearch]
  | fuel + 1, k => by
    simp only [lenSearch]
    split
    · rename_i h; intro _; exact h
    · intro h
      exact lenSearch_stop c r fuel (k + 1) (by omega)

/-- **One repair step.** Only the rank `cumC c b` can get longer, by one level. -/
theorem lenOfRank_repairStep (L : Nat) (c : Nat → Nat) (hL : 1 ≤ L) (hL15 : L ≤ 15) (r : Nat) :
    lenOfRank 15 (repairStep L c) r ≤
      lenOfRank 15 c r + (if r = cumC c (deepest c (L - 1)) then 1 else 0) := by
  have hb := deepest_le_self c (L - 1)
  generalize hB : deepest c (L - 1) = b at hb ⊢
  have cum := cumC_repairStep L c hL b hB
  by_cases found : r ≤ cumC c 15
  · have f := lenOfRank_found c r found
    have lb := lenOfRank_le c r
    generalize hl : lenOfRank 15 c r = l at f lb
    by_cases e : l = b
    · subst e
      by_cases z : c l = 0
      · have := ((cum l).2.1 rfl).2 z
        have := lenOfRank_le_of (repairStep L c) r l lb (by omega)
        omega
      · by_cases top : r = cumC c l
        · rw [ite_eq_left top]
          have up : r ≤ cumC (repairStep L c) (l + 1) := by
            have mono := cumC_mono c (show l ≤ l + 1 by omega)
            by_cases small : l + 1 < L
            · have := (cum (l + 1)).2.2.1 (by omega) small; omega
            · have := (cum (l + 1)).2.2.2 (by omega); omega
          have := lenOfRank_le_of (repairStep L c) r (l + 1) (by omega) up
          omega
        · have := ((cum l).2.1 rfl).1
          have low : r ≤ cumC c l - 1 := by omega
          have := lenOfRank_le_of (repairStep L c) r l lb (by omega)
          omega
    · have up : cumC c l ≤ cumC (repairStep L c) l := by
        by_cases o1 : l < b
        · exact Nat.le_of_eq ((cum l).1 o1).symm
        · by_cases o2 : l < L
          · have := (cum l).2.2.1 (by omega) o2; omega
          · exact (cum l).2.2.2 (by omega)
      have := lenOfRank_le_of (repairStep L c) r l lb (by omega)
      omega
  · have := lenOfRank_le (repairStep L c) r
    have := lenSearch_stop c r 15 0
    have : lenOfRank 15 c r = 15 := by
      apply Nat.le_antisymm (lenOfRank_le c r)
      refine Nat.le_of_not_lt fun hlt => ?_
      have h := this (by simpa [lenOfRank] using hlt)
      have := cumC_mono c (lenOfRank_le c r)
      simp only [lenOfRank] at this
      omega
    omega

theorem sumR_single_le (w : Nat → Nat) (a : Nat) : ∀ n, sumR (fun r => if r = a then w r else 0) n ≤ w a
  | 0 => Nat.zero_le _
  | n + 1 => by
    simp only [sumR]
    have := sumR_single_le w a n
    by_cases e : n + 1 = a
    · subst e
      have zero : sumR (fun r => if r = n + 1 then w r else 0) n = 0 := by
        rw [sumR_congr n (g := fun _ => 0) fun r _ h => by rw [ite_eq_right (by omega)]]
        exact sumR_zero n
      simp only [ite_true]; omega
    · simp only [e, ite_false]; omega

/-- One repair step adds at most the weight of the lengthened rank. -/
theorem cost_repairStep (L : Nat) (w c : Nat → Nat) (hL : 1 ≤ L) (hL15 : L ≤ 15) (N : Nat) :
    sumR (fun r => w r * lenOfRank 15 (repairStep L c) r) N ≤
      sumR (fun r => w r * lenOfRank 15 c r) N + w (cumC c (deepest c (L - 1))) := by
  have step : sumR (fun r => w r * lenOfRank 15 (repairStep L c) r) N ≤
      sumR (fun r => w r * lenOfRank 15 c r + (if r = cumC c (deepest c (L - 1)) then w r else 0)) N := by
    apply sumR_le
    intro r _ _
    have h := Nat.mul_le_mul_left (w r) (lenOfRank_repairStep L c hL hL15 r)
    rw [Nat.mul_add] at h
    split
    · rename_i e; rw [ite_eq_left e] at h; omega
    · rename_i e; rw [ite_eq_right e] at h; omega
  rw [sumR_add] at step
  have := sumR_single_le w (cumC c (deepest c (L - 1))) N
  omega

/-- `M` repair steps add at most `repairExtra`. -/
theorem cost_repairIter (L : Nat) (w : Nat → Nat) (hL : 1 ≤ L) (hL15 : L ≤ 15) (N : Nat) :
    ∀ M (c : Nat → Nat), sumR (fun r => w r * lenOfRank 15 (repairIter L M c) r) N ≤
      sumR (fun r => w r * lenOfRank 15 c r) N + repairExtra L w M c
  | 0, c => by simp [repairIter, repairExtra]
  | M + 1, c => by
    simp only [repairIter, repairExtra]
    have := cost_repairIter L w hL hL15 N M (repairStep L c)
    have := cost_repairStep L w c hL hL15 N
    omega

theorem sumR_shift (w : Nat → Nat) (K : Nat) (hK : 1 ≤ K) : ∀ N,
    sumR (fun r => if K - 1 < r then w r else 0) N =
      sumR (fun r => if K < r then w r else 0) N + (if K ≤ N then w K else 0)
  | 0 => by simp only [sumR]; split <;> omega
  | N + 1 => by
    simp only [sumR]
    rw [sumR_shift w K hK N]
    by_cases k1 : K ≤ N
    · simp only [k1, show K ≤ N + 1 by omega, ite_true, show K - 1 < N + 1 by omega,
        show K < N + 1 by omega]
      omega
    · by_cases k2 : K = N + 1
      · subst k2
        simp only [k1, ite_false, Nat.le_refl, ite_true, show N + 1 - 1 < N + 1 by omega,
          Nat.lt_irrefl]
      · simp only [k1, ite_false, show ¬ K ≤ N + 1 by omega, show ¬ K - 1 < N + 1 by omega,
          show ¬ K < N + 1 by omega]

/-- The lightest suffix of ranks weighs at most any set of ranks at least as large. -/
theorem suffix_le (w : Nat → Nat) (p : Nat → Bool) : ∀ N K,
    (∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y) → N ≤ K + countR p N →
    sumR (fun r => if K < r then w r else 0) N ≤ sumR (fun r => if p r then w r else 0) N
  | 0, _, _, _ => Nat.le_refl _
  | N + 1, K, hw, size => by
    simp only [sumR]
    have hw' : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y := fun y r a b c => hw y r a b (by omega)
    have cnt : countR p (N + 1) = countR p N + (if p (N + 1) then 1 else 0) := rfl
    by_cases e : p (N + 1) = true
    · rw [cnt, ite_eq_left e] at size
      have := suffix_le w p N K hw' (by omega)
      simp only [e, ite_true]
      split <;> omega
    · rw [cnt, ite_eq_right e] at size
      simp only [e]
      have hK : 1 ≤ K := by have := countR_le_n p N; omega
      have := suffix_le w p N (K - 1) hw' (by omega)
      have shift := sumR_shift w K hK N
      have last : (if K < N + 1 then w (N + 1) else 0) ≤ (if K ≤ N then w K else 0) := by
        by_cases k : K ≤ N
        · rw [ite_eq_left (by omega), ite_eq_left k]; exact hw K (N + 1) hK (by omega) (Nat.le_refl _)
        · rw [ite_eq_right (by omega)]; exact Nat.zero_le _
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      omega

/-- Threshold form of `lenOfRank` on a histogram of values `≤ 15`. -/
theorem lenOfRank_hist_gt (m : Nat → Nat) (N : Nat) (hm : ∀ r, 1 ≤ r → r ≤ N → m r ≤ 15)
    (r t : Nat) (_h1 : 1 ≤ r) (h2 : r ≤ N) (_ht : t < 15) :
    t < lenOfRank 15 (fun j => countR (fun r => m r == j) N) r ↔
      countR (fun r => decide (m r ≤ t)) N < r := by
  have hcum := cumC_hist m N
  constructor
  · intro h
    have := lenOfRank_below _ r t h
    rw [hcum t] at this
    exact this
  · intro h
    refine Nat.lt_of_not_le fun hle => ?_
    have all : countR (fun r => decide (m r ≤ 15)) N = N :=
      countR_all _ N fun y a b => by have := hm y a b; simp [this]
    have found := lenOfRank_found (fun j => countR (fun r => m r == j) N) r
      (by rw [hcum 15, all]; exact h2)
    have mono := cumC_mono (fun j => countR (fun r => m r == j) N) hle
    rw [hcum, hcum] at mono
    rw [hcum] at found
    omega

theorem countR_split (p : Nat → Bool) : ∀ N,
    countR p N + countR (fun r => !p r) N = N
  | 0 => rfl
  | N + 1 => by
    have := countR_split p N
    show (countR p N + (if p (N + 1) then 1 else 0)) + (countR (fun r => !p r) N + (if !p (N + 1) then 1 else 0)) = N + 1
    cases p (N + 1) <;> simp <;> omega

/-- **Rearrangement.** With weights nonincreasing in rank, the sorted assignment of a histogram
of values `≤ 15` costs at most the assignment `m` itself. -/
theorem sorted_cost_le (w m : Nat → Nat) (N : Nat)
    (hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y) (hm : ∀ r, 1 ≤ r → r ≤ N → m r ≤ 15) :
    sumR (fun r => w r * lenOfRank 15 (fun j => countR (fun r => m r == j) N) r) N ≤
      sumR (fun r => w r * m r) N := by
  let ls := lenOfRank 15 (fun j => countR (fun r => m r == j) N)
  have stage : ∀ T, T ≤ 15 → sumR (fun r => w r * min (ls r) T) N ≤ sumR (fun r => w r * min (m r) T) N := by
    intro T
    induction T with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have e1 : sumR (fun r => w r * min (ls r) (t + 1)) N =
          sumR (fun r => w r * min (ls r) t) N + sumR (fun r => if t < ls r then w r else 0) N := by
        rw [← sumR_add]; apply sumR_congr; intro r _ _
        by_cases c : t < ls r
        · rw [ite_eq_left c, show min (ls r) (t + 1) = min (ls r) t + 1 by omega, Nat.mul_add, Nat.mul_one]
        · rw [ite_eq_right c, show min (ls r) (t + 1) = min (ls r) t by omega, Nat.add_zero]
      have e2 : sumR (fun r => w r * min (m r) (t + 1)) N =
          sumR (fun r => w r * min (m r) t) N + sumR (fun r => if t < m r then w r else 0) N := by
        rw [← sumR_add]; apply sumR_congr; intro r _ _
        by_cases c : t < m r
        · rw [ite_eq_left c, show min (m r) (t + 1) = min (m r) t + 1 by omega, Nat.mul_add, Nat.mul_one]
        · rw [ite_eq_right c, show min (m r) (t + 1) = min (m r) t by omega, Nat.add_zero]
      let K := countR (fun r => decide (m r ≤ t)) N
      have left : sumR (fun r => if t < ls r then w r else 0) N = sumR (fun r => if K < r then w r else 0) N := by
        apply sumR_congr; intro r a b
        have := lenOfRank_hist_gt m N hm r t a b (by omega)
        by_cases c : K < r
        · rw [ite_eq_left c, ite_eq_left (this.mpr c)]
        · rw [ite_eq_right c, ite_eq_right (fun h => c (this.mp h))]
      have right : sumR (fun r => if t < m r then w r else 0) N =
          sumR (fun r => if (!decide (m r ≤ t)) = true then w r else 0) N := by
        apply sumR_congr; intro r _ _
        by_cases c : t < m r
        · simp [c, show ¬ m r ≤ t by omega]
        · simp [c, show m r ≤ t by omega]
      have size := countR_split (fun r => decide (m r ≤ t)) N
      have suf := suffix_le w (fun r => !decide (m r ≤ t)) N K hw (by omega)
      have := ih (by omega)
      omega
  have := stage 15 (Nat.le_refl _)
  have l : sumR (fun r => w r * min (ls r) 15) N = sumR (fun r => w r * ls r) N :=
    sumR_congr N fun r _ _ => by rw [Nat.min_eq_left (lenOfRank_le _ r)]
  have rr : sumR (fun r => w r * min (m r) 15) N = sumR (fun r => w r * m r) N :=
    sumR_congr N fun r a b => by rw [Nat.min_eq_left (hm r a b)]
  rw [l, rr] at this
  exact this

/-- **H2a, heap-free.** The repaired lengths cost at most the true depths plus the weights of
the ranks the repair lengthens. -/
theorem repair_cost_le (L : Nat) (hL : 1 ≤ L) (hL15 : L ≤ 15) (w δ : Nat → Nat) (N M : Nat)
    (hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y) :
    sumR (fun r => w r * lenOfRank 15 (repairIter L M (histL L δ N)) r) N ≤
      sumR (fun r => w r * δ r) N + repairExtra L w M (histL L δ N) := by
  have iter := cost_repairIter L w hL hL15 N M (histL L δ N)
  have sorted := sorted_cost_le w (fun r => min (δ r) L) N hw (fun r _ _ => by omega)
  have clamp : sumR (fun r => w r * min (δ r) L) N ≤ sumR (fun r => w r * δ r) N :=
    sumR_le N fun r _ _ => Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
  unfold histL at iter ⊢
  omega

end Zlib.Trees.HuffmanAbstract
