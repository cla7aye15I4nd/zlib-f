import ZlibF.Math.DeflateWeightedMass

/-! # Frequency costs and unsigned cancellation for static block selection -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A fresh dummy leaf adds exactly its coefficient to the natural cost. -/
theorem fresh_weighted_cost {frequency coefficient : Nat → Nat} {n key : Nat}
    (fit : key < n) (fresh : frequency key = 0) :
    mass (fun v => (if v = key then 1 else frequency v) * coefficient v) n =
      mass (fun v => frequency v * coefficient v) n + coefficient key := by
  have point : (fun v => (if v = key then 1 else frequency v) * coefficient v) =
      (fun v => frequency v * coefficient v + if v = key then coefficient key else 0) := by
    funext v
    by_cases same : v = key
    · subst v
      simp [fresh]
    · simp [same]
  rw [point, mass_add, mass_single_value, if_pos fit]

/-- The source may temporarily underflow while subtracting a dummy cost.
The later identical contribution cancels in the unsigned word exactly. -/
theorem word_dummy_cancel (word : UInt64) (cost dummy : Nat) :
    (word - UInt64.ofNat dummy) + UInt64.ofNat (cost + dummy) = word + UInt64.ofNat cost := by
  rw [UInt64.ofNat_add, UInt64.add_comm (UInt64.ofNat cost) (UInt64.ofNat dummy),
    ← UInt64.add_assoc, UInt64.sub_add_cancel]

theorem literal_frequency_cost (lengthCode : Nat → Nat) (xs : List Symbol)
    (coefficient : Nat → Nat) (n : Nat) (eob : 256 < n)
    (bounds : ∀ s ∈ xs, s.literalKey lengthCode < n) :
    mass (fun v => literalFrequency lengthCode xs v * coefficient v) n =
      coefficient 256 + (xs.map (fun s => coefficient (s.literalKey lengthCode))).sum := by
  have point : (fun v => literalFrequency lengthCode xs v * coefficient v) =
      (fun v => (if v = 256 then coefficient 256 else 0) +
        countKey (fun s => some (s.literalKey lengthCode)) xs v * coefficient v) := by
    funext v
    unfold literalFrequency
    by_cases same : v = 256
    · subst v
      simp [Nat.add_mul]
    · simp [same]
  rw [point, mass_add, mass_single_value, if_pos eob,
    weighted_count_key (xs := xs) (fun s : Symbol => s.literalKey lengthCode) n coefficient bounds]

/-- Both code alphabets share one per-symbol fixed-bit budget. -/
theorem paired_symbol_cost_bound {α : Type} (xs : List α) (literal distance : α → Nat) (limit : Nat)
    (bound : ∀ s ∈ xs, literal s + distance s ≤ limit) :
    (xs.map literal).sum + (xs.map distance).sum ≤ limit * xs.length := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have head := bound s (by simp)
    have tail := ih (fun t member => bound t (by simp [member]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end ZlibF.Math.DeflateSymbols
