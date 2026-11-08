import ZlibF.Math.DeflateSymbols

/-! # The total weight of a symbol histogram -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def mass (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mass f n + f n

theorem mass_congr {f g : Nat → Nat} {n : Nat} (agree : ∀ k, k < n → f k = g k) :
    mass f n = mass g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mass, ih (fun k bound => agree k (by omega)), agree n (by omega)]

theorem mass_zero (n : Nat) : mass (fun _ => 0) n = 0 := by
  induction n <;> simp_all [mass]

theorem mass_add (f g : Nat → Nat) (n : Nat) :
    mass (fun k => f k + g k) n = mass f n + mass g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mass, ih]; omega

theorem mass_single (n k : Nat) :
    mass (fun j => if j = k then 1 else 0) n = if k < n then 1 else 0 := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    simp only [mass, ih]
    by_cases eq : n = k
    · subst k
      simp
    · by_cases before : k < n
      · simp [before, eq, show k < n + 1 by omega]
      · simp [before, eq, show ¬ k < n + 1 by omega]

theorem mass_count_key {α : Type} (key : α → Nat) {xs : List α} (n : Nat)
    (bounds : ∀ s ∈ xs, key s < n) :
    mass (countKey (fun s => some (key s)) xs) n = xs.length := by
  induction xs with
  | nil => exact mass_zero n
  | cons s xs ih =>
    have first := bounds s (by simp)
    have rest := ih (fun t member => bounds t (by simp [member]))
    have split : countKey (fun s => some (key s)) (s :: xs) =
        fun k => (if k = key s then 1 else 0) + countKey (fun s => some (key s)) xs k := by
      funext k
      simp [countKey, eq_comm]
    rw [split, mass_add, mass_single, if_pos first, rest]
    simp only [List.length_cons]
    omega

theorem mass_optional_key {α : Type} (key : α → Option Nat) {xs : List α} (n : Nat)
    (bounds : ∀ s ∈ xs, ∀ k, key s = some k → k < n) :
    mass (countKey key xs) n ≤ xs.length := by
  induction xs with
  | nil => simp only [countKey]; rw [mass_zero]; simp
  | cons s xs ih =>
    have rest := ih (fun t member => bounds t (by simp [member]))
    rw [show countKey key (s :: xs) =
      (fun k => (if key s = some k then 1 else 0) + countKey key xs k) from rfl, mass_add]
    cases eq : key s with
    | none =>
      simp only [eq, reduceCtorEq, ite_false]
      rw [mass_zero]
      simp only [List.length_cons]
      omega
    | some k =>
      have first := bounds s (by simp) k eq
      have single : (fun j => if some k = some j then 1 else 0) =
          (fun j => if j = k then 1 else 0) := by funext j; simp [eq_comm]
      rw [single, mass_single, if_pos first]
      simp only [List.length_cons]
      omega

theorem literal_frequency_mass (lc : Nat → Nat) {xs : List Symbol}
    (bounds : ∀ s ∈ xs, s.literalKey lc < 286) :
    mass (literalFrequency lc xs) 286 = xs.length + 1 := by
  unfold literalFrequency
  rw [mass_add, mass_single, mass_count_key _ _ bounds]
  simp [Nat.add_comm]

theorem distance_frequency_mass (dc : Nat → Nat) {xs : List Symbol}
    (bounds : ∀ s ∈ xs, ∀ k, s.distanceKey dc = some k → k < 30) :
    mass (distanceFrequency dc xs) 30 ≤ xs.length := mass_optional_key _ _ bounds

end ZlibF.Math.DeflateSymbols
