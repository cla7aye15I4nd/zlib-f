
/-!
# Pure facts behind `gen_bitlen`

* `rs F n = Σ_{i<n} F i` and its algebra (congruence, additivity, single
  point, swap, image/reindexing, counting).
* The clamped-depth identity of a Huffman tree laid out as `build_tree` lays
  it out (`kraft_clamped`): with `ovf` the number of nodes whose depth exceeds
  `L`, the clamped Kraft sum of the leaves is `2^L + ovf/2`, `ovf` is even, and
  `bl_count[L] ≥ ovf/2 + 1` when `ovf > 0`.
* One round of the overflow fix-up lowers the Kraft sum by exactly one.

Everything here is about natural numbers; no heap.
-/

namespace Zlib.Trees.Proofs.GB

/-! ## Finite sums -/

/-- `rs F n = F 0 + … + F (n-1)`. -/
def rs (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rs F n + F n

@[simp] theorem rs_zero (F : Nat → Nat) : rs F 0 = 0 := rfl
theorem rs_succ (F : Nat → Nat) (n : Nat) : rs F (n + 1) = rs F n + F n := rfl

theorem rs_congr {F G : Nat → Nat} {n : Nat} (h : ∀ i < n, F i = G i) : rs F n = rs G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, rs_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem rs_add (F G : Nat → Nat) (n : Nat) : rs (fun i => F i + G i) n = rs F n + rs G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, rs_succ, rs_succ, ih]; omega

theorem rs_mul (c : Nat) (F : Nat → Nat) (n : Nat) : rs (fun i => c * F i) n = c * rs F n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rs_succ, rs_succ, ih, Nat.mul_add]

theorem rs_le {F G : Nat → Nat} {n : Nat} (h : ∀ i < n, F i ≤ G i) : rs F n ≤ rs G n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rs_succ, rs_succ]
    have := ih (fun i hi => h i (by omega)); have := h n (by omega); omega

theorem rs_eq_zero {F : Nat → Nat} {n : Nat} (h : ∀ i < n, F i = 0) : rs F n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem rs_zero_of {F : Nat → Nat} {n : Nat} (h : rs F n = 0) : ∀ i < n, F i = 0 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [rs_succ] at h
    intro i hi
    by_cases e : i = n
    · subst e; omega
    · exact ih (by omega) i (by omega)

theorem le_rs {F : Nat → Nat} {n i : Nat} (hi : i < n) : F i ≤ rs F n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [rs_succ]
    by_cases e : i = n
    · subst e; omega
    · have := ih (by omega); omega

theorem rs_const (c n : Nat) : rs (fun _ => c) n = c * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rs_succ, ih, Nat.mul_succ]

/-- Splitting a range. -/
theorem rs_split (F : Nat → Nat) (a b : Nat) : rs F (a + b) = rs F a + rs (fun i => F (a + i)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, rs_succ, rs_succ, ih, Nat.add_assoc]

/-- Sum of a function supported at one point. -/
theorem rs_single (G : Nat → Nat) (k n : Nat) :
    rs (fun i => if i = k then G i else 0) n = if k < n then G k else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rs_succ, ih]
    by_cases e : n = k
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases h1 : k < n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]; rfl
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem rs_single' (G : Nat → Nat) (k n : Nat) (hk : k < n) :
    rs (fun i => if k = i then G i else 0) n = G k := by
  rw [rs_congr (G := fun i => if i = k then G i else 0) (fun i _ => by
    by_cases e : i = k
    · subst e; simp
    · rw [ite_eq_right (Ne.symm e), ite_eq_right e])]
  rw [rs_single, ite_eq_left hk]

theorem rs_swap (F : Nat → Nat → Nat) (m n : Nat) :
    rs (fun b => rs (fun p => F b p) m) n = rs (fun p => rs (fun b => F b p) n) m := by
  induction n with
  | zero => simp only [rs_zero]; exact (rs_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    rw [rs_succ, ih]
    rw [show (fun p => rs (fun b => F b p) (n + 1)) = (fun p => rs (fun b => F b p) n + F n p) from rfl]
    rw [rs_add]

/-- Changing one term. -/
theorem rs_upd {F G : Nat → Nat} {n k : Nat} (hk : k < n) (h : ∀ i < n, i ≠ k → F i = G i) :
    rs F n + G k = rs G n + F k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [rs_succ, rs_succ]
    by_cases e : k = n
    · subst e
      rw [rs_congr (fun i hi => h i (by omega) (by omega))]; omega
    · have := ih (by omega) (fun i hi hne => h i (by omega) hne)
      rw [h n (by omega) (Ne.symm e)]; omega

/-- All terms `≤ 1` and the sum is `n`: every term is `1`. -/
theorem rs_all_one {F : Nat → Nat} {n : Nat} (hle : ∀ i < n, F i ≤ 1) (hs : rs F n = n) :
    ∀ i < n, F i = 1 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [rs_succ] at hs
    have h1 := hle n (by omega)
    have h2 : rs F n ≤ n := by
      have := rs_le (n := n) (G := fun _ => 1) (fun i hi => hle i (by omega)); rw [rs_const] at this; omega
    intro i hi
    by_cases e : i = n
    · subst e; omega
    · exact ih (fun j hj => hle j (by omega)) (by omega) i (by omega)

/-- Indicator. -/
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem ind_le (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split <;> omega

/-! ## Counting and reindexing -/

/-- Number of `i < m` with `P i = v`. -/
def cnt (P : Nat → Nat) (m v : Nat) : Nat := rs (fun i => if P i = v then 1 else 0) m

/-- **Image lemma.** Summing `F ∘ P` over `i < m` is summing `F v` weighted by
the multiplicity of `v` among `P 0, …, P (m-1)`. -/
theorem rs_image (P F : Nat → Nat) (m N : Nat) (hP : ∀ i < m, P i < N) :
    rs (fun i => F (P i)) m = rs (fun v => cnt P m v * F v) N := by
  induction m with
  | zero =>
    simp only [rs_zero]
    exact (rs_eq_zero (fun v _ => by simp [cnt])).symm
  | succ m ih =>
    rw [rs_succ, ih (fun i hi => hP i (by omega))]
    have e : (fun v => cnt P (m + 1) v * F v) =
        (fun v => cnt P m v * F v + (if v = P m then F v else 0)) := by
      funext v; simp only [cnt, rs_succ]
      by_cases e : P m = v
      · subst e; simp [Nat.add_mul]
      · rw [ite_eq_right e, ite_eq_right (Ne.symm e)]; simp
    rw [e, rs_add, rs_single, ite_eq_left (hP m (by omega))]

theorem cnt_le_one (P : Nat → Nat) (m v : Nat)
    (hinj : ∀ i j, i < m → j < m → P i = P j → i = j) : cnt P m v ≤ 1 := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    simp only [cnt, rs_succ] at *
    have ih' := ih (fun i j hi hj e => hinj i j (by omega) (by omega) e)
    by_cases e : P m = v
    · rw [ite_eq_left e]
      have : rs (fun i => if P i = v then 1 else 0) m = 0 := rs_eq_zero (fun i hi => by
        rw [ite_eq_right]; intro e'; have := hinj i m (by omega) (by omega) (e'.trans e.symm); omega)
      omega
    · rw [ite_eq_right e]; omega

theorem cnt_pos {P : Nat → Nat} {m v i : Nat} (hi : i < m) (e : P i = v) : 1 ≤ cnt P m v := by
  have := le_rs (F := fun i => if P i = v then 1 else 0) hi
  simp only [e, ite_true] at this; exact this

theorem cnt_zero {P : Nat → Nat} {m v : Nat} (h : ∀ i < m, P i ≠ v) : cnt P m v = 0 :=
  rs_eq_zero (fun i hi => by rw [ite_eq_right (h i hi)])

theorem cnt_exists {P : Nat → Nat} {m v : Nat} (h : 1 ≤ cnt P m v) : ∃ i < m, P i = v := by
  by_cases hx : ∃ i < m, P i = v
  · exact hx
  · have := cnt_zero (P := P) (m := m) (v := v) (fun i hi e => hx ⟨i, hi, e⟩); omega

/-- Pigeonhole: an injective map from `m` points into `N` values has `m ≤ N`. -/
theorem inj_le (P : Nat → Nat) (m N : Nat) (hP : ∀ i < m, P i < N)
    (hinj : ∀ i j, i < m → j < m → P i = P j → i = j) : m ≤ N := by
  have := rs_image P (fun _ => 1) m N hP
  rw [rs_const] at this
  have h2 : rs (fun v => cnt P m v * 1) N ≤ rs (fun _ => 1) N :=
    rs_le (fun v _ => by have := cnt_le_one P m v hinj; omega)
  rw [rs_const] at h2; omega

/-- An injective self-map of `[0, n)` hits every point. -/
theorem inj_surj (P : Nat → Nat) (n : Nat) (hP : ∀ i < n, P i < n)
    (hinj : ∀ i j, i < n → j < n → P i = P j → i = j) : ∀ v < n, ∃ i < n, P i = v := by
  have h1 := rs_image P (fun _ => 1) n n hP
  rw [rs_const] at h1
  have := rs_all_one (F := fun v => cnt P n v) (n := n) (fun v _ => cnt_le_one P n v hinj)
    (by rw [← rs_congr (F := fun v => cnt P n v * 1) (fun v _ => by simp)]; omega)
  intro v hv
  exact cnt_exists (by rw [this v hv]; exact Nat.le_refl 1)

/-- Reindexing by a bijection of `[0, n)`. -/
theorem rs_perm (σ F : Nat → Nat) (n : Nat) (hσ : ∀ i < n, σ i < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) : rs (fun i => F (σ i)) n = rs F n := by
  rw [rs_image σ F n n hσ]
  apply rs_congr
  intro v hv
  obtain ⟨i, hi, e⟩ := inj_surj σ n hσ hinj v hv
  have h1 := cnt_pos (P := σ) hi e
  have h2 := cnt_le_one σ n v hinj
  rw [show cnt σ n v = 1 by omega, Nat.one_mul]

/-- Regrouping a sum by the value of a key `f i < B`. -/
theorem rs_regroup (Q : Nat → Prop) [DecidablePred Q] (f W : Nat → Nat) (m B : Nat)
    (hf : ∀ i < m, Q i → f i < B) :
    rs (fun i => if Q i then W (f i) else 0) m =
      rs (fun b => rs (fun i => if Q i ∧ f i = b then 1 else 0) m * W b) B := by
  have e1 : (fun b => rs (fun i => if Q i ∧ f i = b then 1 else 0) m * W b) =
      (fun b => rs (fun i => if Q i ∧ f i = b then W b else 0) m) := by
    funext b
    rw [Nat.mul_comm, ← rs_mul]
    apply rs_congr; intro i _; split <;> simp
  rw [e1, rs_swap]
  apply rs_congr
  intro i hi
  by_cases hq : Q i
  · rw [ite_eq_left hq]
    rw [rs_congr (G := fun b => if f i = b then W b else 0) (fun b _ => by
      by_cases e : f i = b
      · rw [ite_eq_left ⟨hq, e⟩, ite_eq_left e]
      · rw [ite_eq_right (fun h => e h.2), ite_eq_right e])]
    rw [rs_single' W (f i) B (hf i hi hq)]
  · rw [ite_eq_right hq]
    exact (rs_eq_zero (fun b _ => by rw [ite_eq_right (fun h => hq h.1)])).symm

/-- Pairing: `F (t/2)` summed over `t < 2J`... in the `gen_bitlen` order,
position offset `i` belongs to pair `(2J-1-i)/2`. -/
theorem rs_pair (F : Nat → Nat) (J : Nat) :
    rs (fun i => F ((2 * J - 1 - i) / 2)) (2 * J) = 2 * rs F J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show 2 * (J + 1) = 2 + 2 * J by omega, rs_split]
    rw [rs_congr (F := fun i => F ((2 + 2 * J - 1 - (2 + i)) / 2)) (G := fun i => F ((2 * J - 1 - i) / 2))
      (fun i hi => by congr 1; omega)]
    rw [ih, rs_succ]
    simp only [rs_succ, rs_zero]
    rw [show (2 + 2 * J - 1 - 0) / 2 = J by omega, show (2 + 2 * J - 1 - 1) / 2 = J by omega]
    omega

theorem rs_ind_add (p q : Nat → Prop) [DecidablePred p] [DecidablePred q] (n : Nat)
    (h : ∀ i < n, ¬ (p i ∧ q i)) :
    rs (fun i => if p i ∨ q i then 1 else 0) n =
      rs (fun i => if p i then 1 else 0) n + rs (fun i => if q i then 1 else 0) n := by
  rw [← rs_add]; apply rs_congr; intro i hi
  have := h i hi
  by_cases a : p i <;> by_cases b : q i <;> simp_all

end Zlib.Trees.Proofs.GB
