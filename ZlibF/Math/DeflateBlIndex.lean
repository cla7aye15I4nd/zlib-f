import Std.Tactic

/-! # The descending search for the last bit-length code rank

The recursive maximum follows the reference EmitBlTree argument. The lower
bound two reflects the actual loop; a four-code header needs a used rank at
least three, established separately from the caller's constructed trees.
-/

namespace Zlib.Trees.Proofs.Math

def blMaxIdx (used : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => if m + 1 < 3 then m + 1 else if used (m + 1) then m + 1 else blMaxIdx used m

theorem blMaxIdx_le (used : Nat → Bool) (m : Nat) : blMaxIdx used m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih => unfold blMaxIdx; split <;> (try split) <;> omega

theorem blMaxIdx_ge (used : Nat → Bool) (m : Nat) (hm : 2 ≤ m) : 2 ≤ blMaxIdx used m := by
  induction m with
  | zero => omega
  | succ m ih =>
    unfold blMaxIdx
    split
    · omega
    · split
      · omega
      · exact ih (by omega)

theorem blMaxIdx_step (used : Nat → Bool) (m : Nat) (hm : 3 ≤ m) :
    blMaxIdx used m = if used m then m else blMaxIdx used (m - 1) := by
  rw [show m = (m - 1) + 1 by omega]
  simp only [blMaxIdx, ite_eq_right (show ¬ m - 1 + 1 < 3 by omega)]
  simp only [Nat.add_sub_cancel]

/-- Every rank omitted by the returned index has zero length. -/
theorem blMaxIdx_suffix (used : Nat → Bool) (m k : Nat)
    (hk : blMaxIdx used m < k) (hkm : k ≤ m) : used k = false := by
  induction m with
  | zero => have := blMaxIdx_le used 0; omega
  | succ m ih =>
    simp only [blMaxIdx] at hk
    split at hk
    · omega
    · split at hk
      · omega
      · rename_i hu
        by_cases heq : k = m + 1
        · subst k; exact Bool.eq_false_iff.mpr hu
        · exact ih hk (by omega)

/-- A used rank at least three forces enough transmitted header entries. -/
theorem blMaxIdx_ge_of_used (used : Nat → Bool) (m k : Nat)
    (hk3 : 3 ≤ k) (hkm : k ≤ m) (hu : used k = true) : k ≤ blMaxIdx used m := by
  by_cases hle : k ≤ blMaxIdx used m
  · exact hle
  · have hf := blMaxIdx_suffix used m k (by omega) hkm
    rw [hu] at hf
    contradiction

end Zlib.Trees.Proofs.Math
