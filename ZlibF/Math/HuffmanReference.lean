import ZlibF.Proof.«trees.c.heap.gbmath»

/-!
# Huffman optimality against a complete reference code

Heap-free core of the TinyOverlay header bound (H1). `build_tree` leaves its tree in the heap
tail: the removal sequence `nd 0, nd 1, …, nd (2J-1)` (the first removed node first), the root
`nd (2J)`, and internal node `elems + a` with children `nd (2a)`, `nd (2a+1)`. The removal weights
are nondecreasing and a parent weighs the sum of its children (the sibling property). For such
a tree the sum of the internal weights is at most the cost `Σ w·ℓ` of the leaves under every
complete code `ℓ` (`Σ 2^(K-ℓ) = 2^K`, `ℓ ≤ K`), and it equals the cost under the true depths.

The proof is a downward induction over the merges. Stage `a` holds the positions `p ≥ 2a` whose
node is below `elems + a` (the forest after `a` merges). One exchange step moves the two lightest
nodes onto the two longest reference lengths (a complete code has an even, nonzero number of
them) and merges them, which lowers the reference cost by exactly the merged weight.
-/

namespace ZlibF.Math.HuffmanReference
open Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-! ## Finite-sum helpers -/

/-- Changing two terms. -/
theorem rs_two {F G : Nat → Nat} {n a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (h : ∀ p < n, p ≠ a → p ≠ b → F p = G p) : rs F n + G a + G b = rs G n + F a + F b := by
  let H : Nat → Nat := fun p => if p = a then G a else F p
  have e1 : rs F n + H a = rs H n + F a :=
    rs_upd ha (fun p _ hp => by simp only [H, ite_eq_right hp])
  have e2 : rs H n + G b = rs G n + H b := rs_upd hb (fun p hp hpb => by
    by_cases e : p = a
    · subst e; simp only [H, ite_eq_left rfl]
    · simp only [H, ite_eq_right e]; exact h p hp e hpb)
  have hHa : H a = G a := by simp only [H, ite_eq_left rfl]
  have hHb : H b = F b := by simp only [H, ite_eq_right (Ne.symm hab)]
  omega

/-- Changing three terms. -/
theorem rs_three {F G : Nat → Nat} {n a b c : Nat} (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ p < n, p ≠ a → p ≠ b → p ≠ c → F p = G p) :
    rs F n + G a + G b + G c = rs G n + F a + F b + F c := by
  let H : Nat → Nat := fun p => if p = c then G c else F p
  have e1 : rs F n + H c = rs H n + F c :=
    rs_upd hc (fun p _ hp => by simp only [H, ite_eq_right hp])
  have e2 : rs H n + G a + G b = rs G n + H a + H b := rs_two ha hb hab (fun p hp hpa hpb => by
    by_cases e : p = c
    · subst e; simp only [H, ite_eq_left rfl]
    · simp only [H, ite_eq_right e]; exact h p hp hpa hpb e)
  have hHc : H c = G c := by simp only [H, ite_eq_left rfl]
  have hHa : H a = F a := by simp only [H, ite_eq_right hac]
  have hHb : H b = F b := by simp only [H, ite_eq_right hbc]
  omega

theorem rs_ge_two (F : Nat → Nat) {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    F i + F j ≤ rs F n := by
  have two := rs_two (F := F) (G := fun p => if p = i ∨ p = j then 0 else F p) hi hj hij
    (fun p _ hpi hpj => by
      show F p = if p = i ∨ p = j then 0 else F p
      rw [ite_eq_right (fun h => h.elim hpi hpj)])
  try dsimp only at two
  rw [ite_eq_left (Or.inl rfl : i = i ∨ i = j), ite_eq_left (Or.inr rfl : j = i ∨ j = j)] at two
  omega

theorem dvd_rs {d : Nat} {F : Nat → Nat} : ∀ n, (∀ p < n, d ∣ F p) → d ∣ rs F n
  | 0, _ => Nat.dvd_zero d
  | n + 1, h => by
    rw [rs_succ]
    exact Nat.dvd_add (dvd_rs n (fun p hp => h p (by omega))) (h n (by omega))

theorem exists_of_count_pos (P : Nat → Bool) :
    ∀ n, 1 ≤ rs (fun p => if P p then 1 else 0) n → ∃ x < n, P x
  | 0, h => by simp at h
  | n + 1, h => by
    rw [rs_succ] at h
    by_cases e : P n
    · exact ⟨n, by omega, e⟩
    · rw [ite_eq_right e] at h
      obtain ⟨x, hx, px⟩ := exists_of_count_pos P n (by omega)
      exact ⟨x, by omega, px⟩

theorem two_of_count (P : Nat → Bool) :
    ∀ n, 2 ≤ rs (fun p => if P p then 1 else 0) n → ∃ x y, x < n ∧ y < n ∧ x ≠ y ∧ P x ∧ P y
  | 0, h => by simp at h
  | n + 1, h => by
    rw [rs_succ] at h
    by_cases big : 2 ≤ rs (fun p => if P p then 1 else 0) n
    · obtain ⟨x, y, hx, hy, hxy, px, py⟩ := two_of_count P n big
      exact ⟨x, y, by omega, by omega, hxy, px, py⟩
    · have e : P n = true := by
        by_cases e : P n
        · exact e
        · rw [ite_eq_right e] at h; omega
      rw [ite_eq_left e] at h
      obtain ⟨x, hx, px⟩ := exists_of_count_pos P n (by omega)
      exact ⟨x, n, by omega, by omega, by omega, px, e⟩

/-- `wa·lb + wb·la ≤ wa·la + wb·lb` when `wa ≤ wb` and `la ≤ lb` (the exchange inequality). -/
theorem exchange_le {wa wb la lb : Nat} (hw : wa ≤ wb) (hl : la ≤ lb) :
    wa * lb + wb * la ≤ wa * la + wb * lb := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hw
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-! ## Codes on the live positions -/

/-- Kraft sum, scaled by `2^K`, of the live positions below `n`. -/
def kraftA (al : Nat → Bool) (L : Nat → Nat) (K n : Nat) : Nat :=
  rs (fun p => if al p then 2 ^ (K - L p) else 0) n

/-- Cost `Σ w·L` of the live positions below `n`. -/
def costA (al : Nat → Bool) (w L : Nat → Nat) (n : Nat) : Nat :=
  rs (fun p => if al p then w p * L p else 0) n

/-- Exchange the lengths of positions `a` and `b`. -/
def swapL (L : Nat → Nat) (a b : Nat) : Nat → Nat :=
  fun p => if p = a then L b else if p = b then L a else L p

theorem swapL_a (L : Nat → Nat) (a b : Nat) : swapL L a b a = L b := by
  unfold swapL; rw [ite_eq_left rfl]

theorem swapL_b (L : Nat → Nat) {a b : Nat} (h : a ≠ b) : swapL L a b b = L a := by
  unfold swapL; rw [ite_eq_right (Ne.symm h), ite_eq_left rfl]

theorem swapL_o (L : Nat → Nat) {a b p : Nat} (ha : p ≠ a) (hb : p ≠ b) : swapL L a b p = L p := by
  unfold swapL; rw [ite_eq_right ha, ite_eq_right hb]

theorem swapL_self (L : Nat → Nat) (a : Nat) : ∀ p, swapL L a a p = L p := by
  intro p
  by_cases e : p = a
  · rw [e, swapL_a]
  · exact swapL_o L e e

theorem swapL_le (al : Nat → Bool) (L : Nat → Nat) (m : Nat) {n a b : Nat} (ha : a < n) (hb : b < n)
    (aa : al a = true) (ab : al b = true) (h : ∀ p < n, al p = true → L p ≤ m) :
    ∀ p < n, al p = true → swapL L a b p ≤ m := by
  intro p hp ap
  by_cases e1 : p = a
  · rw [e1, swapL_a]; exact h b hb ab
  · by_cases e2 : p = b
    · rw [e2]
      by_cases e3 : b = a
      · rw [e3, swapL_a]; exact h a ha aa
      · rw [swapL_b L (Ne.symm e3)]; exact h a ha aa
    · rw [swapL_o L e1 e2]; exact h p hp ap

theorem kraft_swap (al : Nat → Bool) (L : Nat → Nat) (K : Nat) {n a b : Nat} (ha : a < n) (hb : b < n)
    (aa : al a = true) (ab : al b = true) : kraftA al (swapL L a b) K n = kraftA al L K n := by
  unfold kraftA
  by_cases hab : a = b
  · rw [← hab]
    exact rs_congr (fun p _ => by rw [swapL_self])
  · have two := rs_two (F := fun p => if al p then 2 ^ (K - L p) else 0)
      (G := fun p => if al p then 2 ^ (K - swapL L a b p) else 0) ha hb hab (fun p _ hpa hpb => by
        show (if al p then 2 ^ (K - L p) else 0) = (if al p then 2 ^ (K - swapL L a b p) else 0)
        rw [swapL_o L hpa hpb])
    try dsimp only at two
    rw [ite_eq_left aa, ite_eq_left ab, ite_eq_left aa, ite_eq_left ab, swapL_a, swapL_b L hab] at two
    omega

theorem cost_swap (al : Nat → Bool) (w L : Nat → Nat) {n a b : Nat} (ha : a < n) (hb : b < n)
    (aa : al a = true) (ab : al b = true) (hw : w a ≤ w b) (hl : L a ≤ L b) :
    costA al w (swapL L a b) n ≤ costA al w L n := by
  unfold costA
  by_cases hab : a = b
  · rw [← hab]
    exact Nat.le_of_eq (rs_congr (fun p _ => by rw [swapL_self]))
  · have two := rs_two (F := fun p => if al p then w p * L p else 0)
      (G := fun p => if al p then w p * swapL L a b p else 0) ha hb hab (fun p _ hpa hpb => by
        show (if al p then w p * L p else 0) = (if al p then w p * swapL L a b p else 0)
        rw [swapL_o L hpa hpb])
    try dsimp only at two
    rw [ite_eq_left aa, ite_eq_left ab, ite_eq_left aa, ite_eq_left ab, swapL_a, swapL_b L hab] at two
    have := exchange_le hw hl
    omega

/-- The longest live length. -/
def mxA (al : Nat → Bool) (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if al n then max (mxA al L n) (L n) else mxA al L n

theorem le_mxA (al : Nat → Bool) (L : Nat → Nat) : ∀ n p, p < n → al p = true → L p ≤ mxA al L n
  | 0, _, hp, _ => by omega
  | n + 1, p, hp, ap => by
    simp only [mxA]
    by_cases e : p = n
    · subst e; rw [ite_eq_left ap]; exact Nat.le_max_right _ _
    · have := le_mxA al L n p (by omega) ap
      split
      · exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this

theorem mxA_zero (al : Nat → Bool) (L : Nat → Nat) :
    ∀ n, (∀ p < n, al p = false) → mxA al L n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [mxA]
    rw [ite_eq_right (by rw [h n (by omega)]; decide)]
    exact mxA_zero al L n (fun p hp => h p (by omega))

theorem mxA_attained (al : Nat → Bool) (L : Nat → Nat) :
    ∀ n, (∃ p < n, al p = true) → ∃ p < n, al p = true ∧ L p = mxA al L n
  | 0, ⟨_, hp, _⟩ => by omega
  | n + 1, ⟨p, hp, ap⟩ => by
    simp only [mxA]
    by_cases e : al n = true
    · rw [ite_eq_left e]
      by_cases some : ∃ p < n, al p = true
      · obtain ⟨x, hx, ax, lx⟩ := mxA_attained al L n some
        by_cases le : mxA al L n ≤ L n
        · exact ⟨n, by omega, e, (Nat.max_eq_right le).symm⟩
        · exact ⟨x, by omega, ax, by rw [lx, Nat.max_eq_left (by omega)]⟩
      · have zero : mxA al L n = 0 := mxA_zero al L n (fun p hp => by
          by_cases h : al p = true
          · exact absurd ⟨p, hp, h⟩ some
          · simpa using h)
        exact ⟨n, by omega, e, by rw [zero, Nat.zero_max]⟩
    · rw [ite_eq_right e]
      have hpn : p < n := by
        by_cases q : p = n
        · subst q; exact absurd ap e
        · omega
      obtain ⟨x, hx, ax, lx⟩ := mxA_attained al L n ⟨p, hpn, ap⟩
      exact ⟨x, by omega, ax, lx⟩

/-- A complete code on at least two live positions has two distinct live positions of the
longest length, and that length is positive. -/
theorem complete_two_longest (al : Nat → Bool) (L : Nat → Nat) (K n : Nat) {i j : Nat}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) (ai : al i = true) (aj : al j = true)
    (bound : ∀ p < n, al p = true → L p ≤ K) (kraft : kraftA al L K n = 2 ^ K) :
    1 ≤ mxA al L n ∧ mxA al L n ≤ K ∧
      ∃ x y, x < n ∧ y < n ∧ x ≠ y ∧ al x = true ∧ al y = true ∧
        L x = mxA al L n ∧ L y = mxA al L n := by
  have hle := le_mxA al L n
  obtain ⟨z, hz, az, lz⟩ := mxA_attained al L n ⟨i, hi, ai⟩
  generalize mxA al L n = m at hle lz ⊢
  have mK : m ≤ K := by rw [← lz]; exact bound z hz az
  have m1 : 1 ≤ m := by
    by_cases zero : m = 0
    · have two := rs_ge_two (fun p => if al p then 2 ^ (K - L p) else 0) hi hj hij
      have li : L i = 0 := by have := hle i hi ai; omega
      have lj : L j = 0 := by have := hle j hj aj; omega
      try dsimp only at two
      rw [ite_eq_left ai, ite_eq_left aj, li, lj, Nat.sub_zero] at two
      unfold kraftA at kraft
      have := Nat.one_le_two_pow (n := K)
      omega
    · omega
  refine ⟨m1, mK, ?_⟩
  -- split the Kraft sum at the longest length
  have split : kraftA al L K n =
      rs (fun p => if (al p && L p == m) then 1 else 0) n * 2 ^ (K - m) +
        rs (fun p => if (al p && L p != m) then 2 ^ (K - L p) else 0) n := by
    unfold kraftA
    rw [Nat.mul_comm, ← rs_mul, ← rs_add]
    apply rs_congr
    intro p _
    by_cases ap : al p = true
    · by_cases lp : L p = m
      · simp [ap, lp]
      · simp [ap, lp]
    · simp [ap]
  have dvdR : 2 ^ (K - m + 1) ∣ rs (fun p => if (al p && L p != m) then 2 ^ (K - L p) else 0) n :=
    dvd_rs n (fun p hp => by
      by_cases c : (al p && L p != m) = true
      · rw [ite_eq_left c]
        have ap : al p = true := by simp only [Bool.and_eq_true] at c; exact c.1
        have lp : L p ≠ m := by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at c; exact c.2
        have := hle p hp ap
        exact Nat.pow_dvd_pow 2 (by omega)
      · rw [ite_eq_right c]; exact Nat.dvd_zero _)
  obtain ⟨t, ht⟩ := dvdR
  have top : 2 ^ K = 2 ^ (K - m) * (2 * 2 ^ (m - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  have below : 2 ^ (K - m + 1) = 2 ^ (K - m) * 2 := by rw [Nat.pow_succ]
  rw [kraft, ht, below, top] at split
  have pos : 0 < 2 ^ (K - m) := Nat.two_pow_pos _
  have even : 2 * 2 ^ (m - 1) = rs (fun p => if (al p && L p == m) then 1 else 0) n + 2 * t := by
    apply Nat.eq_of_mul_eq_mul_left pos
    rw [split, Nat.mul_add, Nat.mul_comm (2 ^ (K - m)) (rs _ n), Nat.mul_assoc]
  have cz : 1 ≤ rs (fun p => if (al p && L p == m) then 1 else 0) n := by
    have one := le_rs (F := fun p => if (al p && L p == m) then 1 else 0) hz
    have c : (al z && L z == m) = true := by simp [az, lz]
    try dsimp only at one
    rw [ite_eq_left c] at one
    exact one
  obtain ⟨x, y, hx, hy, hxy, px, py⟩ := two_of_count (fun p => al p && L p == m) n (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq] at px py
  exact ⟨x, y, hx, hy, hxy, px.1, py.1, px.2, py.2⟩

/-- Give position `q` the length `v`. -/
def mergeL (L : Nat → Nat) (q v : Nat) : Nat → Nat := fun p => if p = q then v else L p

theorem live_false {al al' : Nat → Bool} {n i j q p : Nat} (hp : p < n)
    (next : ∀ p < n, (al' p = true ↔ (al p = true ∧ p ≠ i ∧ p ≠ j) ∨ p = q))
    (h : ¬ ((al p = true ∧ p ≠ i ∧ p ≠ j) ∨ p = q)) : al' p = false := by
  by_cases e : al' p = true
  · exact absurd ((next p hp).mp e) h
  · simpa using e

/-- **One merge.** If `i`, `j` are the two lightest live positions and `q` (not live) carries
their merged weight, then every complete code on the live positions costs at least
`w i + w j` more than some complete code on the live positions after the merge. -/
theorem exchange_step (al al' : Nat → Bool) (w L : Nat → Nat) (K n : Nat) {i j q : Nat}
    (hi : i < n) (hj : j < n) (hq : q < n) (hij : i ≠ j)
    (ai : al i = true) (aj : al j = true) (aq : al q = false)
    (mini : ∀ p < n, al p = true → p ≠ i → w i ≤ w p)
    (minj : ∀ p < n, al p = true → p ≠ i → p ≠ j → w j ≤ w p)
    (hwq : w q = w i + w j)
    (next : ∀ p < n, (al' p = true ↔ (al p = true ∧ p ≠ i ∧ p ≠ j) ∨ p = q))
    (bound : ∀ p < n, al p = true → L p ≤ K) (kraft : kraftA al L K n = 2 ^ K) :
    ∃ L', (∀ p < n, al' p = true → L' p ≤ K) ∧ kraftA al' L' K n = 2 ^ K ∧
      costA al' w L' n + w i + w j ≤ costA al w L n := by
  obtain ⟨m1, mK, x, y, hx, hy, hxy, ax, ay, lx, ly⟩ :=
    complete_two_longest al L K n hi hj hij ai aj bound kraft
  have hle := le_mxA al L n
  generalize mxA al L n = m at m1 mK lx ly hle
  have qi : q ≠ i := by intro e; rw [e, ai] at aq; exact absurd aq (by decide)
  have qj : q ≠ j := by intro e; rw [e, aj] at aq; exact absurd aq (by decide)
  -- first swap: `i` takes a longest length
  have k1 : kraftA al (swapL L i x) K n = 2 ^ K := (kraft_swap al L K hi hx ai ax).trans kraft
  have c1 : costA al w (swapL L i x) n ≤ costA al w L n := cost_swap al w L hi hx ai ax
    (by by_cases e : x = i
        · rw [e]; exact Nat.le_refl _
        · exact mini x hx ax e)
    (by rw [lx]; exact hle i hi ai)
  have L1i : swapL L i x i = m := by rw [swapL_a]; exact lx
  have L1le := swapL_le al L m hi hx ai ax hle
  generalize swapL L i x = L1 at k1 c1 L1i L1le
  -- (the value of `L1` at the other longest position)
  obtain ⟨y', hy', ay', yi, L1y⟩ : ∃ y', y' < n ∧ al y' = true ∧ y' ≠ i ∧ L1 y' = m := by
    -- among the live positions, `L1` takes the value `m` at least twice
    have count : 2 ≤ rs (fun p => if (al p && L1 p == m) then 1 else 0) n := by
      have hk := complete_two_longest al L1 K n hi hj hij ai aj (fun p hp ap => by
        have := L1le p hp ap; omega) k1
      obtain ⟨_, _, x2, y2, hx2, hy2, hxy2, ax2, ay2, lx2, ly2⟩ := hk
      have mx : mxA al L1 n = m := by
        have := le_mxA al L1 n i hi ai
        have := L1le
        obtain ⟨z, hz, az, lz⟩ := mxA_attained al L1 n ⟨i, hi, ai⟩
        have := L1le z hz az
        omega
      rw [mx] at lx2 ly2
      have two := rs_ge_two (fun p => if (al p && L1 p == m) then 1 else 0) hx2 hy2 hxy2
      try dsimp only at two
      rw [ite_eq_left (by simp [ax2, lx2]), ite_eq_left (by simp [ay2, ly2])] at two
      exact two
    obtain ⟨u, v, hu, hv, huv, pu, pv⟩ := two_of_count (fun p => al p && L1 p == m) n count
    simp only [Bool.and_eq_true, beq_iff_eq] at pu pv
    by_cases e : u = i
    · exact ⟨v, hv, pv.1, fun h => huv (e.trans h.symm), pv.2⟩
    · exact ⟨u, hu, pu.1, e, pu.2⟩
  -- second swap: `j` takes it
  have k2 : kraftA al (swapL L1 j y') K n = 2 ^ K := (kraft_swap al L1 K hj hy' aj ay').trans k1
  have c2 : costA al w (swapL L1 j y') n ≤ costA al w L1 n := cost_swap al w L1 hj hy' aj ay'
    (by by_cases e : y' = j
        · rw [e]; exact Nat.le_refl _
        · exact minj y' hy' ay' yi e)
    (by rw [L1y]; exact L1le j hj aj)
  have L2i : swapL L1 j y' i = m := by rw [swapL_o L1 hij (Ne.symm yi)]; exact L1i
  have L2j : swapL L1 j y' j = m := by rw [swapL_a]; exact L1y
  have L2le := swapL_le al L1 m hj hy' aj ay' L1le
  generalize swapL L1 j y' = L2 at k2 c2 L2i L2j L2le
  -- merge: the parent takes `m - 1`
  have a'i : al' i = false := live_false hi next (by omega)
  have a'j : al' j = false := live_false hj next (by omega)
  have a'q : al' q = true := (next q hq).mpr (Or.inr rfl)
  have nq : ¬ (al q = true) := by rw [aq]; decide
  have ni : ¬ (al' i = true) := by rw [a'i]; decide
  have nj : ¬ (al' j = true) := by rw [a'j]; decide
  have Mq : mergeL L2 q (m - 1) q = m - 1 := by unfold mergeL; rw [ite_eq_left rfl]
  have Mo : ∀ p, p ≠ q → mergeL L2 q (m - 1) p = L2 p := by
    intro p e; unfold mergeL; rw [ite_eq_right e]
  refine ⟨mergeL L2 q (m - 1), ?_, ?_, ?_⟩
  · intro p hp ap'
    rcases (next p hp).mp ap' with ⟨ap, _, _⟩ | e
    · by_cases e : p = q
      · rw [e, Mq]; omega
      · rw [Mo p e]; have := L2le p hp ap; omega
    · rw [e, Mq]; omega
  · have same : ∀ p < n, p ≠ i → p ≠ j → p ≠ q →
        (fun p => if al p then 2 ^ (K - L2 p) else 0) p =
          (fun p => if al' p then 2 ^ (K - mergeL L2 q (m - 1) p) else 0) p := by
      intro p hp pi pj pq
      dsimp only
      rw [Mo p pq]
      by_cases ap : al p = true
      · rw [ite_eq_left ap, ite_eq_left ((next p hp).mpr (Or.inl ⟨ap, pi, pj⟩))]
      · rw [live_false hp next (fun h => h.elim (fun h1 => ap h1.1) pq)]
        simp only [Bool.not_eq_true] at ap
        rw [ap]
    have three := rs_three hi hj hq hij (Ne.symm qi) (Ne.symm qj) same
    try dsimp only at three
    rw [ite_eq_left ai, ite_eq_left aj, ite_eq_right nq,
      ite_eq_right ni, ite_eq_right nj, ite_eq_left a'q,
      L2i, L2j, Mq] at three
    unfold kraftA
    unfold kraftA at k2
    have dbl : 2 ^ (K - (m - 1)) = 2 ^ (K - m) + 2 ^ (K - m) := by
      rw [show K - (m - 1) = (K - m) + 1 by omega, Nat.pow_succ]; omega
    omega
  · have same : ∀ p < n, p ≠ i → p ≠ j → p ≠ q →
        (fun p => if al p then w p * L2 p else 0) p =
          (fun p => if al' p then w p * mergeL L2 q (m - 1) p else 0) p := by
      intro p hp pi pj pq
      dsimp only
      rw [Mo p pq]
      by_cases ap : al p = true
      · rw [ite_eq_left ap, ite_eq_left ((next p hp).mpr (Or.inl ⟨ap, pi, pj⟩))]
      · rw [live_false hp next (fun h => h.elim (fun h1 => ap h1.1) pq)]
        simp only [Bool.not_eq_true] at ap
        rw [ap]
    have three := rs_three hi hj hq hij (Ne.symm qi) (Ne.symm qj) same
    try dsimp only at three
    rw [ite_eq_left ai, ite_eq_left aj, ite_eq_right nq,
      ite_eq_right ni, ite_eq_right nj, ite_eq_left a'q,
      L2i, L2j, Mq, hwq] at three
    unfold costA
    unfold costA at c1 c2
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm', show m' + 1 - 1 = m' by omega] at three ⊢
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at three
    omega

/-- **A Kraft-deficient code can be completed without lengthening.** If the live lengths satisfy
`Σ 2^(K-ℓ) ≤ 2^K` (and some position is live), shortening the longest length one step at a time
reaches a complete code `ℓ' ≤ ℓ`. -/
theorem complete_of_deficient (al : Nat → Bool) (K n : Nat) (live : ∃ p < n, al p = true) :
    ∀ N (ℓ : Nat → Nat), rs (fun p => if al p then ℓ p else 0) n = N →
      (∀ p < n, al p = true → ℓ p ≤ K) → kraftA al ℓ K n ≤ 2 ^ K →
      ∃ ℓ' : Nat → Nat, (∀ p < n, al p = true → ℓ' p ≤ ℓ p) ∧ kraftA al ℓ' K n = 2 ^ K := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro ℓ hN bound kraft
    by_cases full : kraftA al ℓ K n = 2 ^ K
    · exact ⟨ℓ, fun _ _ _ => Nat.le_refl _, full⟩
    have lt : kraftA al ℓ K n < 2 ^ K := by omega
    have hle := le_mxA al ℓ n
    obtain ⟨z, hz, az, lz⟩ := mxA_attained al ℓ n live
    generalize mxA al ℓ n = m at hle lz
    have mK : m ≤ K := by rw [← lz]; exact bound z hz az
    have m1 : 1 ≤ m := by
      by_cases zero : m = 0
      · have one := le_rs (F := fun p => if al p then 2 ^ (K - ℓ p) else 0) hz
        try dsimp only at one
        rw [ite_eq_left az, lz, zero, Nat.sub_zero] at one
        unfold kraftA at lt
        omega
      · omega
    -- shorten position `z` by one
    have Mz : mergeL ℓ z (m - 1) z = m - 1 := by unfold mergeL; rw [ite_eq_left rfl]
    have Mo : ∀ p, p ≠ z → mergeL ℓ z (m - 1) p = ℓ p := by
      intro p e; unfold mergeL; rw [ite_eq_right e]
    have kr := rs_upd (F := fun p => if al p then 2 ^ (K - ℓ p) else 0)
      (G := fun p => if al p then 2 ^ (K - mergeL ℓ z (m - 1) p) else 0) hz
      (fun p _ e => by (try dsimp only); rw [Mo p e])
    have sm := rs_upd (F := fun p => if al p then mergeL ℓ z (m - 1) p else 0)
      (G := fun p => if al p then ℓ p else 0) hz
      (fun p _ e => by (try dsimp only); rw [Mo p e])
    try dsimp only at kr sm
    rw [ite_eq_left az, ite_eq_left az, Mz, lz] at kr
    rw [ite_eq_left az, ite_eq_left az, Mz, lz, hN] at sm
    have dbl : 2 ^ (K - (m - 1)) = 2 ^ (K - m) + 2 ^ (K - m) := by
      rw [show K - (m - 1) = (K - m) + 1 by omega, Nat.pow_succ]; omega
    -- the old sum and `2^K` are multiples of `2^(K-m)`
    have d1 : 2 ^ (K - m) ∣ kraftA al ℓ K n := dvd_rs n (fun p hp => by
      by_cases ap : al p = true
      · rw [ite_eq_left ap]
        have := hle p hp ap
        exact Nat.pow_dvd_pow 2 (by omega)
      · rw [ite_eq_right ap]; exact Nat.dvd_zero _)
    have d2 : 2 ^ (K - m) ∣ 2 ^ K := Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨a, ha⟩ := d1
    obtain ⟨b, hb⟩ := d2
    have pos : 0 < 2 ^ (K - m) := Nat.two_pow_pos _
    have ab : a < b := by
      rw [ha, hb] at lt
      exact Nat.lt_of_mul_lt_mul_left lt
    have step : 2 ^ (K - m) * (a + 1) ≤ 2 ^ (K - m) * b := Nat.mul_le_mul_left _ ab
    unfold kraftA at ha
    obtain ⟨ℓ', le', full'⟩ := ih (N - 1) (by omega) (mergeL ℓ z (m - 1)) (by omega)
      (fun p hp ap => by
        by_cases e : p = z
        · rw [e, Mz]; omega
        · rw [Mo p e]; exact bound p hp ap)
      (by
        unfold kraftA
        rw [Nat.mul_add, Nat.mul_one, ← ha, ← hb] at step
        omega)
    refine ⟨ℓ', fun p hp ap => ?_, full'⟩
    have := le' p hp ap
    by_cases e : p = z
    · rw [e, Mz] at this; rw [e]; omega
    · rw [Mo p e] at this; exact this

/-! ## The heap tree -/

/-- The tree `build_tree` leaves in the heap tail, with the removal sequence as positions:
`nd p = heap[572 - p]`. Node `elems + a` has children `nd (2a)` and `nd (2a+1)` and appears
later; weights `wN` are nondecreasing in removal order and a parent weighs its two children. -/
structure SibTree (nd wN : Nat → Nat) (J elems : Nat) : Prop where
  J1 : 1 ≤ J
  inj : ∀ p p', p ≤ 2 * J → p' ≤ 2 * J → nd p = nd p' → p = p'
  kind : ∀ p, p ≤ 2 * J → nd p < elems + J
  root : nd (2 * J) = elems + J - 1
  appears : ∀ a < J, ∃ p, 2 * a + 1 < p ∧ p ≤ 2 * J ∧ nd p = elems + a
  sums : ∀ a < J, wN (elems + a) = wN (nd (2 * a)) + wN (nd (2 * a + 1))
  ordered : ∀ p p', p ≤ p' → p' < 2 * J → wN (nd p) ≤ wN (nd p')

/-- The forest after `a` merges, as live positions. -/
def stage (nd : Nat → Nat) (elems a : Nat) : Nat → Bool :=
  fun p => decide (2 * a ≤ p ∧ nd p < elems + a)

section tree
variable {nd wN : Nat → Nat} {J elems : Nat}

/-- A node at position `p` below its parent `elems + a` was created before merge `a`. -/
theorem SibTree.child_below (S : SibTree nd wN J elems) {a p : Nat} (ha : a < J) (hp : p ≤ 2 * a + 1) :
    nd p < elems + a := by
  by_cases lt : nd p < elems
  · omega
  · have := S.kind p (by omega)
    obtain ⟨p', h1, h2, e⟩ := S.appears (nd p - elems) (by omega)
    have := S.inj p' p h2 (by omega) (by rw [e]; omega)
    omega

theorem SibTree.stage_next (S : SibTree nd wN J elems) {a q : Nat} (ha : a < J)
    (hq : q ≤ 2 * J) (eq : nd q = elems + a) :
    ∀ p < 2 * J + 1, (stage nd elems (a + 1) p = true ↔
      (stage nd elems a p = true ∧ p ≠ 2 * a ∧ p ≠ 2 * a + 1) ∨ p = q) := by
  intro p hp
  have q2 : 2 * a + 1 < q := by
    obtain ⟨p', h1, h2, e⟩ := S.appears a ha
    have := S.inj p' q h2 hq (by rw [e, eq])
    omega
  simp only [stage, decide_eq_true_eq]
  constructor
  · intro ⟨h1, h2⟩
    by_cases e : nd p = elems + a
    · right; exact S.inj p q (by omega) hq (by rw [e, eq])
    · left; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro h
    rcases h with ⟨⟨h1, h2⟩, h3, h4⟩ | e
    · exact ⟨by omega, by omega⟩
    · subst e; exact ⟨by omega, by omega⟩

/-- **Stage bound.** At stage `a`, the remaining merge weights are at most the cost of every
complete code on the forest. -/
theorem SibTree.stage_bound (S : SibTree nd wN J elems) (K : Nat) :
    ∀ k, k ≤ J → ∀ L : Nat → Nat,
      (∀ p < 2 * J + 1, stage nd elems (J - k) p = true → L p ≤ K) →
      kraftA (stage nd elems (J - k)) L K (2 * J + 1) = 2 ^ K →
      rs (fun b => wN (elems + (J - k) + b)) k ≤
        costA (stage nd elems (J - k)) (fun p => wN (nd p)) L (2 * J + 1) := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp
  | succ k ih =>
    intro hk L bound kraft
    let a := J - (k + 1)
    have ha : a < J := by omega
    have succA : J - k = a + 1 := by omega
    obtain ⟨q, hq1, hq2, eq⟩ := S.appears a ha
    have next := S.stage_next ha hq2 eq
    have live : ∀ p, p ≤ 2 * a + 1 → 2 * a ≤ p → stage nd elems a p = true := by
      intro p h1 h2
      simp only [stage, decide_eq_true_eq]
      exact ⟨h2, S.child_below ha h1⟩
    have notRoot : ∀ p < 2 * J + 1, stage nd elems a p = true → p < 2 * J := by
      intro p hp ap
      simp only [stage, decide_eq_true_eq] at ap
      by_cases e : p = 2 * J
      · subst e; rw [S.root] at ap; omega
      · omega
    obtain ⟨L', bound', kraft', cost'⟩ := exchange_step (stage nd elems a) (stage nd elems (a + 1))
      (fun p => wN (nd p)) L K (2 * J + 1) (i := 2 * a) (j := 2 * a + 1) (q := q)
      (by omega) (by omega) (by omega) (by omega) (live _ (by omega) (Nat.le_refl _))
      (live _ (Nat.le_refl _) (by omega))
      (by simp only [stage, eq, decide_eq_false_iff_not]; omega)
      (fun p hp ap pi => by
        have := notRoot p hp ap
        simp only [stage, decide_eq_true_eq] at ap
        exact S.ordered _ _ (by omega) this)
      (fun p hp ap pi pj => by
        have := notRoot p hp ap
        simp only [stage, decide_eq_true_eq] at ap
        exact S.ordered _ _ (by omega) this)
      (by show wN (nd q) = _; rw [eq]; exact S.sums a ha)
      next
      (by intro p hp ap; exact bound p hp (by rw [show J - (k + 1) = a from rfl]; exact ap))
      kraft
    have recur := ih (by omega) L' (by rw [succA]; exact bound') (by rw [succA]; exact kraft')
    rw [succA] at recur
    have shift : rs (fun b => wN (elems + a + b)) (k + 1) =
        wN (elems + a) + rs (fun b => wN (elems + (a + 1) + b)) k := by
      rw [show k + 1 = 1 + k by omega, rs_split]
      simp only [rs_succ, rs_zero, Nat.zero_add, Nat.add_zero]
      congr 1
      apply rs_congr; intro b _; congr 1; omega
    show rs (fun b => wN (elems + a + b)) (k + 1) ≤
      costA (stage nd elems a) (fun p => wN (nd p)) L (2 * J + 1)
    rw [shift, S.sums a ha]
    have := cost'
    omega

/-- **H1 core.** The sum of the internal weights is at most the cost of the leaves under every
complete code `ℓ` (`Σ_leaves 2^(K-ℓ) = 2^K`, `ℓ ≤ K` on the leaves). -/
theorem SibTree.internal_le_complete (S : SibTree nd wN J elems) (K : Nat) (L : Nat → Nat)
    (bound : ∀ p < 2 * J + 1, nd p < elems → L p ≤ K)
    (kraft : rs (fun p => if nd p < elems then 2 ^ (K - L p) else 0) (2 * J + 1) = 2 ^ K) :
    rs (fun b => wN (elems + b)) J ≤
      rs (fun p => if nd p < elems then wN (nd p) * L p else 0) (2 * J + 1) := by
  have st := S.stage_bound K J (Nat.le_refl J) L
    (by intro p hp ap; simp only [Nat.sub_self, stage, decide_eq_true_eq] at ap; exact bound p hp (by omega))
    (by
      unfold kraftA; rw [← kraft]
      apply rs_congr; intro p _
      simp only [Nat.sub_self, stage, Nat.mul_zero, Nat.zero_le, true_and, Nat.add_zero, decide_eq_true_eq])
  have lhs : rs (fun b => wN (elems + (J - J) + b)) J = rs (fun b => wN (elems + b)) J :=
    rs_congr (fun b _ => by rw [Nat.sub_self, Nat.add_zero])
  have rhs : costA (stage nd elems (J - J)) (fun p => wN (nd p)) L (2 * J + 1) =
      rs (fun p => if nd p < elems then wN (nd p) * L p else 0) (2 * J + 1) := by
    unfold costA
    apply rs_congr; intro p _
    simp only [Nat.sub_self, stage, Nat.mul_zero, Nat.zero_le, true_and, Nat.add_zero, decide_eq_true_eq]
  rw [lhs, rhs] at st
  exact st

/-- **H1 depth identity.** With `dl` the true depth (root 0, each child one deeper), the sum of
the internal weights is the depth cost of the leaves. -/
theorem SibTree.internal_eq_depth (S : SibTree nd wN J elems) (dl : Nat → Nat)
    (hroot : dl (elems + J - 1) = 0)
    (hchild : ∀ a < J, dl (nd (2 * a)) = dl (elems + a) + 1 ∧ dl (nd (2 * a + 1)) = dl (elems + a) + 1) :
    rs (fun b => wN (elems + b)) J =
      rs (fun p => if nd p < elems then wN (nd p) * dl (nd p) else 0) (2 * J + 1) := by
  -- downward over the stages, with the depth cost at every stage
  have key : ∀ k, k ≤ J → rs (fun b => wN (elems + (J - k) + b)) k =
      costA (stage nd elems (J - k)) (fun p => wN (nd p)) (fun p => dl (nd p)) (2 * J + 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.sub_zero, rs_zero, costA]
      -- stage J is the root alone, at depth 0
      symm
      apply rs_eq_zero
      intro p hp
      by_cases ap : stage nd elems J p = true
      · simp only [stage, decide_eq_true_eq] at ap
        have : p = 2 * J := by omega
        subst this
        rw [S.root, hroot]; simp
      · simp only [Bool.not_eq_true] at ap; simp [ap]
    | succ k ih =>
      intro hk
      let a := J - (k + 1)
      have ha : a < J := by omega
      have succA : J - k = a + 1 := by omega
      obtain ⟨q, hq1, hq2, eq⟩ := S.appears a ha
      have next := S.stage_next ha hq2 eq
      have recur := ih (by omega)
      rw [succA] at recur
      have shift : rs (fun b => wN (elems + a + b)) (k + 1) =
          wN (elems + a) + rs (fun b => wN (elems + (a + 1) + b)) k := by
        rw [show k + 1 = 1 + k by omega, rs_split]
        simp only [rs_succ, rs_zero, Nat.zero_add, Nat.add_zero]
        congr 1
        apply rs_congr; intro b _; congr 1; omega
      have i0 : 2 * a < 2 * J + 1 := by omega
      have j0 : 2 * a + 1 < 2 * J + 1 := by omega
      have q0 : q < 2 * J + 1 := by omega
      have qi : q ≠ 2 * a := by omega
      have qj : q ≠ 2 * a + 1 := by omega
      have same : ∀ p < 2 * J + 1, p ≠ 2 * a → p ≠ 2 * a + 1 → p ≠ q →
          (if stage nd elems a p then wN (nd p) * dl (nd p) else 0) =
            (if stage nd elems (a + 1) p then wN (nd p) * dl (nd p) else 0) := by
        intro p hp pi pj pq
        have iff := next p hp
        by_cases ap : stage nd elems a p = true
        · rw [ite_eq_left ap, ite_eq_left (iff.mpr (Or.inl ⟨ap, pi, pj⟩))]
        · have ap' : stage nd elems (a + 1) p = false := by
            by_cases h : stage nd elems (a + 1) p = true
            · rcases iff.mp h with ⟨h1, _⟩ | h2
              · exact absurd h1 ap
              · exact absurd h2 pq
            · simpa using h
          simp only [Bool.not_eq_true] at ap
          rw [ap, ap']
      have three := rs_three i0 j0 q0 (by omega) (Ne.symm qi) (Ne.symm qj) same
      have s_i : stage nd elems a (2 * a) = true := by
        simp only [stage, decide_eq_true_eq]; exact ⟨Nat.le_refl _, S.child_below ha (by omega)⟩
      have s_j : stage nd elems a (2 * a + 1) = true := by
        simp only [stage, decide_eq_true_eq]; exact ⟨by omega, S.child_below ha (Nat.le_refl _)⟩
      have s_q : stage nd elems a q = false := by
        simp only [stage, eq, decide_eq_false_iff_not]; omega
      have t_i : stage nd elems (a + 1) (2 * a) = false := by
        simp only [stage, decide_eq_false_iff_not]; omega
      have t_j : stage nd elems (a + 1) (2 * a + 1) = false := by
        simp only [stage, decide_eq_false_iff_not]; omega
      have t_q : stage nd elems (a + 1) q = true := by
        simp only [stage, eq, decide_eq_true_eq]; omega
      obtain ⟨d1, d2⟩ := hchild a ha
      simp only [s_i, s_j, s_q, t_i, t_j, t_q, ite_true, Bool.false_eq_true, ite_false, eq] at three
      rw [d1, d2] at three
      have stepCost : rs (fun p => if stage nd elems a p then wN (nd p) * dl (nd p) else 0) (2 * J + 1) =
          wN (elems + a) +
            rs (fun p => if stage nd elems (a + 1) p then wN (nd p) * dl (nd p) else 0) (2 * J + 1) := by
        rw [S.sums a ha]
        rw [S.sums a ha] at three
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at three
        omega
      have recur' : rs (fun b => wN (elems + (a + 1) + b)) k =
          rs (fun p => if stage nd elems (a + 1) p then wN (nd p) * dl (nd p) else 0) (2 * J + 1) := recur
      show rs (fun b => wN (elems + a + b)) (k + 1) =
        rs (fun p => if stage nd elems a p then wN (nd p) * dl (nd p) else 0) (2 * J + 1)
      rw [shift, recur', stepCost]
  have top := key J (Nat.le_refl J)
  have lhs : rs (fun b => wN (elems + (J - J) + b)) J = rs (fun b => wN (elems + b)) J :=
    rs_congr (fun b _ => by rw [Nat.sub_self, Nat.add_zero])
  have rhs : costA (stage nd elems (J - J)) (fun p => wN (nd p)) (fun p => dl (nd p)) (2 * J + 1) =
      rs (fun p => if nd p < elems then wN (nd p) * dl (nd p) else 0) (2 * J + 1) := by
    unfold costA
    apply rs_congr; intro p _
    simp only [Nat.sub_self, stage, Nat.mul_zero, Nat.zero_le, true_and, Nat.add_zero, decide_eq_true_eq]
  rw [lhs, rhs] at top
  exact top

/-- **H1 (heap-free).** The true-depth cost of the leaves is at most their cost under every
complete code. -/
theorem SibTree.depth_le_complete (S : SibTree nd wN J elems) (dl : Nat → Nat)
    (hroot : dl (elems + J - 1) = 0)
    (hchild : ∀ a < J, dl (nd (2 * a)) = dl (elems + a) + 1 ∧ dl (nd (2 * a + 1)) = dl (elems + a) + 1)
    (K : Nat) (L : Nat → Nat) (bound : ∀ p < 2 * J + 1, nd p < elems → L p ≤ K)
    (kraft : rs (fun p => if nd p < elems then 2 ^ (K - L p) else 0) (2 * J + 1) = 2 ^ K) :
    rs (fun p => if nd p < elems then wN (nd p) * dl (nd p) else 0) (2 * J + 1) ≤
      rs (fun p => if nd p < elems then wN (nd p) * L p else 0) (2 * J + 1) := by
  rw [← S.internal_eq_depth dl hroot hchild]
  exact S.internal_le_complete K L bound kraft

/-- **H1 (heap-free, Kraft ≤ 1).** The true-depth cost of the leaves is at most their cost under
every prefix code `ℓ` (`Σ_leaves 2^(K-ℓ) ≤ 2^K`, `ℓ ≤ K`). -/
theorem SibTree.depth_le_kraft (S : SibTree nd wN J elems) (dl : Nat → Nat)
    (hroot : dl (elems + J - 1) = 0)
    (hchild : ∀ a < J, dl (nd (2 * a)) = dl (elems + a) + 1 ∧ dl (nd (2 * a + 1)) = dl (elems + a) + 1)
    (K : Nat) (L : Nat → Nat) (bound : ∀ p < 2 * J + 1, nd p < elems → L p ≤ K)
    (kraft : rs (fun p => if nd p < elems then 2 ^ (K - L p) else 0) (2 * J + 1) ≤ 2 ^ K) :
    rs (fun p => if nd p < elems then wN (nd p) * dl (nd p) else 0) (2 * J + 1) ≤
      rs (fun p => if nd p < elems then wN (nd p) * L p else 0) (2 * J + 1) := by
  let al : Nat → Bool := fun p => decide (nd p < elems)
  have alIff : ∀ p, al p = true ↔ nd p < elems := fun p => by simp [al]
  have conv : ∀ F : Nat → Nat, rs (fun p => if al p then F p else 0) (2 * J + 1) =
      rs (fun p => if nd p < elems then F p else 0) (2 * J + 1) := by
    intro F; apply rs_congr; intro p _
    by_cases c : nd p < elems
    · rw [ite_eq_left ((alIff p).mpr c), ite_eq_left c]
    · rw [ite_eq_right (fun h => c ((alIff p).mp h)), ite_eq_right c]
  have live : ∃ p < 2 * J + 1, al p = true :=
    ⟨0, by omega, (alIff 0).mpr (by have := S.child_below (a := 0) (p := 0) (by have := S.J1; omega) (by omega); omega)⟩
  obtain ⟨L', le', full'⟩ := complete_of_deficient al K (2 * J + 1) live _ L rfl
    (fun p hp ap => bound p hp ((alIff p).mp ap)) (by unfold kraftA; rw [conv]; exact kraft)
  have main := S.depth_le_complete dl hroot hchild K L'
    (fun p hp leaf => Nat.le_trans (le' p hp ((alIff p).mpr leaf)) (bound p hp leaf))
    (by have := full'; unfold kraftA at this; rw [conv] at this; exact this)
  refine Nat.le_trans main (rs_le (fun p hp => ?_))
  by_cases c : nd p < elems
  · rw [ite_eq_left c, ite_eq_left c]
    exact Nat.mul_le_mul_left _ (le' p hp ((alIff p).mpr c))
  · rw [ite_eq_right c, ite_eq_right c]; exact Nat.le_refl 0

end tree

end ZlibF.Math.HuffmanReference
