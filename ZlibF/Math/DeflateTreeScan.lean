import Std

/-! # Counting the leaves inserted by the first `build_tree` scan -/

namespace Zlib.Trees.Math

/-- Number of positive-frequency symbols below the scan position. -/
def scanCount (fr : Nat → UInt16) : Nat → Nat
  | 0 => 0
  | k + 1 => scanCount fr k + if fr k ≠ 0 then 1 else 0

/-- Largest positive-frequency symbol below the scan position, or `-1`. -/
def scanMax (fr : Nat → UInt16) : Nat → Int
  | 0 => -1
  | k + 1 => if fr k ≠ 0 then k else scanMax fr k

theorem scanCount_le (fr : Nat → UInt16) (k : Nat) : scanCount fr k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => simp only [scanCount]; split <;> omega

theorem scanMax_bounds (fr : Nat → UInt16) (k : Nat) :
    -1 ≤ scanMax fr k ∧ scanMax fr k < k := by
  induction k with
  | zero => simp [scanMax]
  | succ k ih => simp only [scanMax]; split <;> omega

/-- The selected maximum is exact, including the all-zero case. -/
theorem scanMax_spec (fr : Nat → UInt16) (k : Nat) :
    (scanMax fr k = -1 ∧ ∀ m < k, fr m = 0) ∨
    (∃ u : Nat, scanMax fr k = u ∧ u < k ∧ fr u ≠ 0 ∧
      ∀ m, u < m → m < k → fr m = 0) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, by omega⟩
  | succ k ih =>
    simp only [scanMax]
    by_cases hk : fr k ≠ 0
    · rw [ite_eq_left hk]
      exact Or.inr ⟨k, rfl, by omega, hk, by omega⟩
    · rw [ite_eq_right hk]
      rcases ih with ⟨he, hz⟩ | ⟨u, he, hu, hf, hz⟩
      · refine Or.inl ⟨he, ?_⟩
        intro m hm
        by_cases heq : m = k
        · subst m; simpa using hk
        · exact hz m (by omega)
      · refine Or.inr ⟨u, he, by omega, hf, ?_⟩
        intro m hm1 hm2
        by_cases heq : m = k
        · subst m; simpa using hk
        · exact hz m hm1 (by omega)

end Zlib.Trees.Math
