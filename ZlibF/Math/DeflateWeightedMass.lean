import ZlibF.Math.DeflateTreeWeight

/-! # Weighted source symbol histograms and their integer cost bounds -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem mass_mul_left (f : Nat → Nat) (n c : Nat) : mass (fun k => c * f k) n = c * mass f n := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp only [mass, ih, Nat.mul_add]

theorem mass_mul_right (f : Nat → Nat) (n c : Nat) : mass (fun k => f k * c) n = mass f n * c := by
  induction n with
  | zero => simp [mass]
  | succ n ih => simp only [mass, ih, Nat.add_mul]

theorem mass_single_value (n key value : Nat) :
    mass (fun k => if k = key then value else 0) n = if key < n then value else 0 := by
  have point : (fun k => if k = key then value else 0) = (fun k => (if k = key then 1 else 0) * value) := by
    funext k
    by_cases same : k = key <;> simp only [same, ite_true, ite_false, Nat.one_mul, Nat.zero_mul]
  rw [point, mass_mul_right, mass_single]
  split <;> simp

/-- A histogram weighted by code cost equals the sum of costs over the
original source symbols, including repeated occurrences of the same code. -/
theorem weighted_count_key {α : Type} (key : α → Nat) {xs : List α} (n : Nat) (cost : Nat → Nat)
    (bounds : ∀ x ∈ xs, key x < n) :
    mass (fun k => countKey (fun x => some (key x)) xs k * cost k) n =
      (xs.map (fun x => cost (key x))).sum := by
  induction xs with
  | nil => simp only [countKey, Nat.zero_mul, List.map_nil, List.sum_nil]; exact mass_zero n
  | cons x xs ih =>
    have first := bounds x (by simp)
    have rest := ih (fun y member => bounds y (by simp [member]))
    have point : (fun k => countKey (fun x => some (key x)) (x :: xs) k * cost k) =
        (fun k => (if k = key x then cost (key x) else 0) + countKey (fun x => some (key x)) xs k * cost k) := by
      funext k
      by_cases same : k = key x
      · subst k
        simp only [countKey, ite_true, Nat.add_mul, Nat.one_mul]
      · simp [countKey, same, Ne.symm same]
    rw [point, mass_add, mass_single_value, if_pos first, rest]
    simp only [List.map_cons, List.sum_cons]

/-- Pointwise code certificates add to a whole-tree cost bound. Zero-count
codes contribute no left-hand cost. The class budget is used once globally. -/
theorem weighted_tree_bound (frequency cost coefficient push : Nat → Nat)
    (n lambda mu weight budget : Nat)
    (codes : ∀ k, k < n → frequency k ≠ 0 →
      frequency k * (1000 * cost k) ≤ lambda * frequency k + coefficient k * weight + mu * push k * weight)
    (pushBound : mass push n ≤ budget) :
    1000 * mass (fun k => frequency k * cost k) n ≤
      lambda * mass frequency n + (mass coefficient n + mu * budget) * weight := by
  have point : ∀ k, k < n → 1000 * (frequency k * cost k) ≤
      lambda * frequency k + coefficient k * weight + mu * push k * weight := by
    intro k bound
    by_cases zero : frequency k = 0
    · simp only [zero, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
      omega
    · simpa only [Nat.mul_left_comm] using codes k bound zero
  have combined := mass_mono point
  simp only [mass_add, mass_mul_left, mass_mul_right] at combined
  have bounded := Nat.mul_le_mul_right weight (Nat.mul_le_mul_left mu pushBound)
  rw [Nat.add_mul]
  omega

/-- Every occurrence contributes one to its selected histogram entry. -/
theorem count_key_positive {α : Type} (key : α → Option Nat) {xs : List α} {x : α} {v : Nat}
    (member : x ∈ xs) (selected : key x = some v) : 1 ≤ countKey key xs v := by
  induction xs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    rcases member with same | rest
    · subst x
      rw [countKey, selected, if_pos rfl]
      omega
    · have previous := ih rest
      rw [countKey]
      omega

/-- Optional histograms omit unselected symbols and otherwise retain the
exact weighted contribution of every occurrence. -/
theorem weighted_optional_key {α : Type} (key : α → Option Nat) {xs : List α} (n : Nat) (cost : Nat → Nat)
    (bounds : ∀ x ∈ xs, ∀ k, key x = some k → k < n) :
    mass (fun k => countKey key xs k * cost k) n =
      (xs.map (fun x => match key x with | none => 0 | some k => cost k)).sum := by
  induction xs with
  | nil => simp only [countKey, Nat.zero_mul, List.map_nil, List.sum_nil]; exact mass_zero n
  | cons x xs ih =>
    have rest := ih (fun y member => bounds y (by simp [member]))
    cases selected : key x with
    | none =>
      have same : (fun k => countKey key (x :: xs) k * cost k) =
          (fun k => countKey key xs k * cost k) := by
        funext k
        simp only [countKey, selected, reduceCtorEq, ite_false, Nat.zero_add]
      rw [same, rest]
      simp only [List.map_cons, selected, List.sum_cons, Nat.zero_add]
    | some v =>
      have first := bounds x (by simp) v selected
      have point : (fun k => countKey key (x :: xs) k * cost k) =
          (fun k => (if k = v then cost v else 0) + countKey key xs k * cost k) := by
        funext k
        by_cases same : k = v
        · subst k
          simp only [countKey, selected, ite_true, Nat.add_mul, Nat.one_mul]
        · simp [countKey, selected, same, Ne.symm same]
      rw [point, mass_add, mass_single_value, if_pos first, rest]
      simp only [List.map_cons, selected, List.sum_cons]

theorem list_sum_le_split {α : Type} (xs : List α) (cost left right : α → Nat)
    (bound : ∀ x ∈ xs, cost x ≤ left x + right x) :
    (xs.map cost).sum ≤ (xs.map left).sum + (xs.map right).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have first := bound x (by simp)
    have rest := ih (fun y member => bound y (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

end ZlibF.Math.DeflateSymbols
