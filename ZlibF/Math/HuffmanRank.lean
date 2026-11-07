import ZlibF.Math.HuffmanRepair
import ZlibF.Math.HuffmanPushModel

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# Ranks, cumulative counts and weighted sums (helpers for `FibPush`)

* `sumR f n = f 1 + … + f n` (spec file), and `countR p n` counts the ranks `1 ≤ r ≤ n` with `p r`.
* `wsum wt c j = Σ_{i ≤ j} c i · wt i`, with `cumC c j = wsum 1 c j` and
  `krS c j = wsum (2^(15−·)) c j` (the Kraft sum of a count profile at scale `2^15`).
* `lenOfRank 15 c r` is characterized by `lenOfRank_eq`.
-/

namespace Zlib.Trees.HuffmanAbstract

/-! ## Rank sums -/

/-- The number of ranks `1 ≤ r ≤ n` with `p r`. -/
def countR (p : Nat → Bool) (n : Nat) : Nat := sumR (fun r => if p r then 1 else 0) n

theorem sumR_le {f g : Nat → Nat} : ∀ n, (∀ r, 1 ≤ r → r ≤ n → f r ≤ g r) → sumR f n ≤ sumR g n
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
    have := sumR_le n fun r h1 h2 => h r h1 (by omega)
    have := h (n + 1) (by omega) (Nat.le_refl _)
    simp only [sumR]; omega

theorem sumR_add (f g : Nat → Nat) : ∀ n, sumR (fun r => f r + g r) n = sumR f n + sumR g n
  | 0 => rfl
  | n + 1 => by simp only [sumR, sumR_add f g n]; omega

theorem sumR_single (a v : Nat) : ∀ n, sumR (fun r => if r = a then v else 0) n ≤ v := by
  intro n
  have : ∀ n, sumR (fun r => if r = a then v else 0) n = if 1 ≤ a ∧ a ≤ n then v else 0 := by
    intro n
    induction n with
    | zero => simp [sumR]; omega
    | succ n ih =>
      simp only [sumR, ih]
      by_cases h1 : n + 1 = a
      · subst h1; simp; omega
      · by_cases h2 : 1 ≤ a ∧ a ≤ n
        · simp [h1, h2]; omega
        · rw [if_neg h1, if_neg h2, if_neg (by omega)]
  rw [this]; split <;> omega

theorem sumR_zero : ∀ n, sumR (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [sumR, sumR_zero n]

theorem countR_le_n (p : Nat → Bool) : ∀ n, countR p n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by
    have := countR_le_n p n
    simp only [countR, sumR] at this ⊢; split <;> omega

theorem countR_mono (p : Nat → Bool) {m n : Nat} (h : m ≤ n) : countR p m ≤ countR p n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · have := ih (by omega); simp only [countR, sumR] at this ⊢; omega
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Pigeonhole: fewer than `r` of the ranks `1 .. r` satisfy `p`, so one does not. -/
theorem exists_not_of_countR_lt (p : Nat → Bool) : ∀ r, countR p r < r → ∃ y, 1 ≤ y ∧ y ≤ r ∧ p y = false
  | 0, h => by simp [countR, sumR] at h
  | r + 1, h => by
    by_cases hp : p (r + 1) = true
    · have h' : countR p r < r := by simp only [countR, sumR, hp] at h ⊢; simp at h; omega
      obtain ⟨y, h1, h2, h3⟩ := exists_not_of_countR_lt p r h'
      exact ⟨y, h1, by omega, h3⟩
    · exact ⟨r + 1, by omega, Nat.le_refl _, by simpa using hp⟩

/-- The ranks `≤ a` among `1 .. n` number at most `a`. -/
theorem countR_le_bound (a : Nat) : ∀ n, sumR (fun r => if r ≤ a then 1 else 0) n ≤ a := by
  intro n
  have : ∀ n, sumR (fun r => if r ≤ a then 1 else 0) n = min a n := by
    intro n; induction n with
    | zero => simp [sumR]
    | succ n ih => simp only [sumR, ih]; split <;> omega
  rw [this]; omega

/-! ## Weighted cumulative sums -/

/-- `Σ_{i ≤ j} c i · wt i`. -/
def wsum (wt c : Nat → Nat) : Nat → Nat
  | 0 => c 0 * wt 0
  | j + 1 => wsum wt c j + c (j + 1) * wt (j + 1)

/-- The Kraft sum `Σ_{i ≤ j} c i · 2^(15 − i)` of a count profile. -/
def krS (c : Nat → Nat) (j : Nat) : Nat := wsum (fun i => 2 ^ (15 - i)) c j

theorem cumC_eq_wsum (c : Nat → Nat) : ∀ j, cumC c j = wsum (fun _ => 1) c j
  | 0 => by simp [cumC, wsum]
  | j + 1 => by simp [cumC, wsum, cumC_eq_wsum c j]

theorem wsum_congr {wt c c' : Nat → Nat} : ∀ j, (∀ i, i ≤ j → c i = c' i) → wsum wt c j = wsum wt c' j
  | 0, h => by simp [wsum, h 0 (Nat.le_refl _)]
  | j + 1, h => by
    simp only [wsum, h (j + 1) (Nat.le_refl _), wsum_congr j fun i hi => h i (by omega)]

/-- Moving one unit from level `b` to level `a`: if `f i + [i = a] = g i + [i = b]` for all `i`,
then `wsum f j + [a ≤ j]·wt a = wsum g j + [b ≤ j]·wt b`. -/
theorem wsum_shift (wt f g : Nat → Nat) (a b : Nat)
    (h : ∀ i, f i + (if i = a then 1 else 0) = g i + (if i = b then 1 else 0)) :
    ∀ j, wsum wt f j + (if a ≤ j then wt a else 0) = wsum wt g j + (if b ≤ j then wt b else 0) := by
  have hm : ∀ i, f i * wt i + (if i = a then wt a else 0) = g i * wt i + (if i = b then wt b else 0) := by
    intro i
    have hi := h i
    by_cases ha : i = a <;> by_cases hb : i = b
    · subst ha; subst hb; simp at hi ⊢; rw [hi]
    · subst ha; simp only [if_true, if_neg hb, Nat.add_zero] at hi ⊢; rw [← hi, Nat.add_mul, Nat.one_mul]
    · subst hb; simp only [if_true, if_neg ha, Nat.add_zero] at hi ⊢; rw [hi, Nat.add_mul, Nat.one_mul]
    · simp only [if_neg ha, if_neg hb] at hi ⊢; simp at hi; rw [hi]
  intro j
  induction j with
  | zero =>
    have := hm 0
    simp only [wsum]
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · subst ha; subst hb; simp at this ⊢; omega
    · subst ha; simp [show ¬ b ≤ 0 by omega, show ¬ (0 = b) by omega] at this ⊢; omega
    · subst hb; simp [show ¬ a ≤ 0 by omega, show ¬ (0 = a) by omega] at this ⊢; omega
    · simp [show ¬ a ≤ 0 by omega, show ¬ b ≤ 0 by omega, show ¬ (0 = a) by omega,
        show ¬ (0 = b) by omega] at this ⊢; omega
  | succ j ih =>
    have := hm (j + 1)
    simp only [wsum]
    by_cases ha : a = j + 1 <;> by_cases hb : b = j + 1
    · subst ha; subst hb; simp at ih this ⊢; omega
    · subst ha
      rw [if_neg (by omega)] at ih; rw [if_pos (Nat.le_refl _)]
      simp only [if_true, show ¬ (j + 1 = b) by omega, if_false] at this
      by_cases hb' : b ≤ j
      · rw [if_pos hb'] at ih; rw [if_pos (by omega)]; omega
      · rw [if_neg hb'] at ih; rw [if_neg (by omega)]; omega
    · subst hb
      rw [if_neg (show ¬ (j + 1 ≤ j) by omega)] at ih; rw [if_pos (Nat.le_refl (j + 1))]
      simp only [if_true, show ¬ (j + 1 = a) by omega, if_false] at this
      by_cases ha' : a ≤ j
      · rw [if_pos ha'] at ih; rw [if_pos (by omega)]; omega
      · rw [if_neg ha'] at ih; rw [if_neg (by omega)]; omega
    · simp only [show ¬ (j + 1 = a) by omega, show ¬ (j + 1 = b) by omega, if_false] at this
      have e1 : (a ≤ j + 1) = (a ≤ j) := by apply propext; omega
      have e2 : (b ≤ j + 1) = (b ≤ j) := by apply propext; omega
      simp only [e1, e2]; omega

theorem cumC_mono (c : Nat → Nat) {i j : Nat} (h : i ≤ j) : cumC c i ≤ cumC c j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega); simp only [cumC]; omega
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

theorem cumC_congr {c c' : Nat → Nat} (j : Nat) (h : ∀ i, i ≤ j → c i = c' i) : cumC c j = cumC c' j := by
  rw [cumC_eq_wsum, cumC_eq_wsum]; exact wsum_congr j h

/-- Levels `s+1 .. j` empty: the cumulative count does not grow. -/
theorem cumC_flat (c : Nat → Nat) (s : Nat) : ∀ j, s ≤ j → (∀ i, s < i → i ≤ j → c i = 0) → cumC c j = cumC c s
  | 0, h, _ => by have : s = 0 := by omega
                  subst this; rfl
  | j + 1, h, hz => by
    rcases Nat.lt_or_ge s (j + 1) with h' | h'
    · simp only [cumC]; rw [hz (j + 1) h' (Nat.le_refl _), cumC_flat c s j (by omega)
        fun i h1 h2 => hz i h1 (by omega), Nat.add_zero]
    · have : s = j + 1 := by omega
      subst this; rfl

/-! ## `lenOfRank` -/

theorem lenSearch_spec (c : Nat → Nat) (r : Nat) : ∀ fuel k,
    k ≤ lenSearch c r k fuel ∧ lenSearch c r k fuel ≤ k + fuel ∧
      (∀ j, k ≤ j → j < lenSearch c r k fuel → cumC c j < r) ∧
      (r ≤ cumC c (k + fuel) → r ≤ cumC c (lenSearch c r k fuel))
  | 0, k => by simp [lenSearch]; intro j h1 h2; omega
  | fuel + 1, k => by
    simp only [lenSearch]
    split
    · rename_i h; refine ⟨Nat.le_refl _, by omega, fun j h1 h2 => by omega, fun _ => h⟩
    · rename_i h
      obtain ⟨h1, h2, h3, h4⟩ := lenSearch_spec c r fuel (k + 1)
      refine ⟨by omega, by omega, fun j hj1 hj2 => ?_, fun hr => h4 (by rw [show k + 1 + fuel = k + (fuel + 1) by omega]; exact hr)⟩
      rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · have : j = k := by omega
        subst this; omega
      · exact h3 j hj hj2

theorem lenOfRank_le (c : Nat → Nat) (r : Nat) : lenOfRank 15 c r ≤ 15 := by
  have := (lenSearch_spec c r 15 0).2.1; simpa [lenOfRank] using this

theorem lenOfRank_below (c : Nat → Nat) (r : Nat) : ∀ j, j < lenOfRank 15 c r → cumC c j < r := by
  intro j hj; exact (lenSearch_spec c r 15 0).2.2.1 j (Nat.zero_le _) hj

theorem lenOfRank_found (c : Nat → Nat) (r : Nat) (h : r ≤ cumC c 15) : r ≤ cumC c (lenOfRank 15 c r) :=
  (lenSearch_spec c r 15 0).2.2.2 (by simpa using h)

theorem lenOfRank_le_of (c : Nat → Nat) (r j : Nat) (_hj : j ≤ 15) (h : r ≤ cumC c j) : lenOfRank 15 c r ≤ j := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := lenOfRank_below c r j hlt; omega

/-- **Characterization of `lenOfRank`.** -/
theorem lenOfRank_eq (c : Nat → Nat) (r ℓ : Nat) (hℓ : ℓ ≤ 15) (hb : ∀ j, j < ℓ → cumC c j < r)
    (hf : r ≤ cumC c ℓ) : lenOfRank 15 c r = ℓ := by
  have h1 := lenOfRank_le_of c r ℓ hℓ hf
  refine Nat.le_antisymm h1 (Nat.le_of_not_lt fun hlt => ?_)
  have := lenOfRank_found c r (Nat.le_trans hf (cumC_mono c hℓ))
  have := hb _ hlt; omega

end Zlib.Trees.HuffmanAbstract
