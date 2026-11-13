import ZlibF.Proof.«trees.c.overlay-scan-cost»

/-!
# trees.c: the cost of `scan_tree`'s bit-length symbols with charges per region

`scan_cost_le` charges every zero 2 bits. At `lit_bufsize = 128` that is too weak: a run of zeros
costs one `REPZ` symbol however long it is. Here the charges are general:

* a nonzero entry of length `x` at position `i` is charged `P x + A i`;
* a zero at position `i` is charged `B i`.

A run of zeros is paid by its zeros (`B` each) and by the credit `A` of the nonzero entry that
ends it; a full run of 138 zeros followed by more zeros is paid by its zeros alone. `A` and `B`
are constant along a run of zeros (`keep`), so a region whose last entry is nonzero (the literal
region ends with the end-of-block code) pays its own runs. The conditions on the weights `wt`
(the cost of the bit-length symbols, scaled) are the run costs of `scan_tree`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass mass_add mass_congr mass_zero)
set_option autoImplicit false

/-- The conditions on the charges for the bit-length symbol weights `wt`. -/
structure ScanCharges (wt P A B : Nat → Nat) : Prop where
  short : ∀ x, 1 ≤ x → x ≤ 15 → wt x ≤ P x
  rep : ∀ x, 1 ≤ x → x ≤ 15 → wt 16 ≤ 3 * P x
  zero1 : ∀ i, wt 0 ≤ A i + B i
  zero2 : ∀ i, 2 * wt 0 ≤ A i + 2 * B i
  zero3 : ∀ i, wt 17 ≤ A i + 3 * B i
  zero11 : ∀ i, wt 18 ≤ A i + 11 * B i
  full : ∀ i, wt 18 ≤ 138 * B i

theorem run_point (wt : Nat → Nat) (c a : Nat) (hc : c < 19) (g : Nat → Nat) (hg : ∀ k, g k = if k = c then a else 0) :
    mass (fun k => g k * wt k) 19 = a * wt c := by
  rw [mass_congr (g := fun k => (if k = c then a else 0) * wt k) (fun k _ => by rw [hg k])]
  exact mass_point wt c a 19 hc

/-- A run of a nonzero length costs at most its count times `P`. -/
theorem run_cost_nonzero (wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (cur : Nat) (prev : Int)
    (cnt mn : Nat) (nz : cur ≠ 0) (small : cur ≤ 15)
    (shape : mn ≤ cnt → 3 ≤ cnt ∧ ((cur : Int) ≠ prev → 4 ≤ cnt)) :
    mass (fun k => runFreq (some (cur, prev, cnt, mn)) k * wt k) 19 ≤ cnt * P cur := by
  have s1 := ch.short cur (by omega) small
  have s16 := ch.rep cur (by omega) small
  by_cases few : cnt < mn
  · rw [run_point wt cur cnt (by omega) _ (fun k => by simp [runFreq, few])]
    exact Nat.mul_le_mul_left _ s1
  have ⟨three, four⟩ := shape (by omega)
  by_cases newLen : (cur : Int) ≠ prev
  · have f4 := four newLen
    have split : mass (fun k => runFreq (some (cur, prev, cnt, mn)) k * wt k) 19 =
        mass (fun k => (if k = cur then 1 else 0) * wt k) 19 +
          mass (fun k => (if k = 16 then 1 else 0) * wt k) 19 := by
      rw [← mass_add]
      apply mass_congr
      intro k _
      simp only [runFreq, few, if_false, nz, newLen, ne_eq, not_false_eq_true, if_true, true_and]
      rw [Nat.add_mul]
    rw [split, mass_point wt cur 1 19 (by omega), mass_point wt 16 1 19 (by omega)]
    have : cnt * P cur ≥ 4 * P cur := Nat.mul_le_mul_right _ f4
    omega
  · have same : (cur : Int) = prev := by simpa using newLen
    rw [run_point wt 16 1 (by omega) _ (fun k => by simp [runFreq, few, nz, same])]
    have : cnt * P cur ≥ 3 * P cur := Nat.mul_le_mul_right _ three
    omega

/-- A run of zeros costs at most the credit `A` plus `B` per zero; a full run of 138 costs at most
`B` per zero. -/
theorem run_cost_zero (wt P A B : Nat → Nat) (ch : ScanCharges wt P A B) (i : Nat) (prev : Int)
    (cnt mn : Nat) (one : 1 ≤ cnt) (mn3 : mn = 3) :
    mass (fun k => runFreq (some (0, prev, cnt, mn)) k * wt k) 19 ≤ A i + cnt * B i ∧
      (cnt = 138 → mass (fun k => runFreq (some (0, prev, cnt, mn)) k * wt k) 19 ≤ cnt * B i) := by
  subst mn3
  have z1 := ch.zero1 i
  have z2 := ch.zero2 i
  have z3 := ch.zero3 i
  have z11 := ch.zero11 i
  have zf := ch.full i
  by_cases few : cnt < 3
  · rw [run_point wt 0 cnt (by omega) _ (fun k => by simp [runFreq, few])]
    refine ⟨?_, fun e => by omega⟩
    rcases (show cnt = 1 ∨ cnt = 2 by omega) with e | e <;> subst e <;> omega
  by_cases ten : cnt ≤ 10
  · rw [run_point wt 17 1 (by omega) _ (fun k => by simp [runFreq, few, ten])]
    have : cnt * B i ≥ 3 * B i := Nat.mul_le_mul_right _ (by omega)
    exact ⟨by omega, fun e => by omega⟩
  · rw [run_point wt 18 1 (by omega) _ (fun k => by simp [runFreq, few, ten])]
    have : cnt * B i ≥ 11 * B i := Nat.mul_le_mul_right _ (by omega)
    exact ⟨by omega, fun e => by subst e; omega⟩

/-- The charge of entry `i`. -/
def regionCharge (L P A B : Nat → Nat) (i : Nat) : Nat := if L i = 0 then B i else P (L i) + A i

/-- **The scan with region charges**: the bit-length symbols of the first `n` iterations, plus the
pending run at its charge, cost at most the charges of the first `n` entries, plus the credit of
entry `n` if a run of zeros ended just before it. -/
theorem scan_cost_region_pending (L wt P A B : Nat → Nat) (ch : ScanCharges wt P A B)
    (hL : ∀ n, L n < 2 ^ 16) (keep : ∀ i, L i = 0 → A (i + 1) = A i ∧ B (i + 1) = B i) (n : Nat)
    (small : ∀ i, i < n → L i ≤ 15) :
    mass (fun k => scanFreqUpTo L n k * wt k) 19 +
        (runAt L n).cnt * (if L n = 0 then B n else P (L n)) ≤
      mass (regionCharge L P A B) n + (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) := by
  induction n with
  | zero =>
    simp only [scanFreqUpTo, Nat.zero_mul, runAt, runInit]
    rw [mass_zero 19]
    split <;> simp [mass]
  | succ n ih =>
    have prevBound := ih (fun i lt => small i (by omega))
    have inv := runInv_runAt L hL n
    have nextEq := runAt_next L n
    have smallN := small n (by omega)
    have rhs : mass (regionCharge L P A B) (n + 1) = mass (regionCharge L P A B) n + regionCharge L P A B n := rfl
    have lhs : mass (fun k => scanFreqUpTo L (n + 1) k * wt k) 19 =
        mass (fun k => scanFreqUpTo L n k * wt k) 19 +
          mass (fun k => runFreq (runStep L n (runAt L n)).2 k * wt k) 19 :=
      mass_mul_add _ _ _ 19
    have stepEq : runAt L (n + 1) = (runStep L n (runAt L n)).1 := rfl
    rw [rhs, lhs, stepEq]
    generalize runAt L n = s at prevBound inv nextEq ⊢
    obtain ⟨hlt, zeroShape, nzShape, _, _⟩ := inv
    have chN : regionCharge L P A B n = if L n = 0 then B n else P (L n) + A n := rfl
    rw [chN, Nat.add_sub_cancel]
    by_cases cont : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
    · -- the run goes on: no cost, one more pending entry of the same length
      have h2 : (runStep L n s).2 = none := by simp [runStep, cont]
      have h1 : (runStep L n s).1.cnt = s.cnt + 1 := by simp [runStep, cont]
      have none : mass (fun k => runFreq none k * wt k) 19 = 0 := by
        simp only [runFreq, Nat.zero_mul]; exact mass_zero 19
      rw [h2, h1, none]
      have e : L (n + 1) = L n := by rw [← cont.2, nextEq]
      rw [e]
      have expandB : (s.cnt + 1) * B n = s.cnt * B n + B n := by rw [Nat.add_mul, Nat.one_mul]
      have expandP : (s.cnt + 1) * P (L n) = s.cnt * P (L n) + P (L n) := by rw [Nat.add_mul, Nat.one_mul]
      have d1 : (if 0 < n + 1 ∧ L n = 0 ∧ L n ≠ 0 then A (n + 1) else 0) = 0 := by
        rw [if_neg (by intro h; exact h.2.2 h.2.1)]
      rw [d1]
      by_cases z : L n = 0
      · have kb := (keep n z).2
        have d0 : (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) = 0 := by
          rw [if_neg (by intro h; exact h.2.2 z)]
        rw [d0, if_pos z] at prevBound
        rw [if_pos z, if_pos z, kb]
        omega
      · have dle : (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) ≤ A n := by split <;> omega
        rw [if_neg z] at prevBound
        rw [if_neg z, if_neg z]
        omega
    · -- the run ends at n
      have h2 : (runStep L n s).2 = some (s.next, s.prev, s.cnt + 1, s.mn) := by simp [runStep, cont]
      have h1 : (runStep L n s).1.cnt = 0 := by
        unfold runStep
        simp only [cont, if_false]
        split
        · rfl
        · split <;> rfl
      rw [h2, h1, Nat.zero_mul, Nat.add_zero]
      by_cases z : s.next = 0
      · -- a run of zeros
        have ⟨mx138, mn3⟩ := zeroShape z
        have Ln : L n = 0 := by rw [← nextEq]; exact z
        have run := run_cost_zero wt P A B ch n s.prev (s.cnt + 1) s.mn (by omega) mn3
        rw [z]
        have d0 : (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) = 0 := by
          rw [if_neg (by intro h; exact h.2.2 Ln)]
        rw [d0, if_pos Ln] at prevBound
        rw [if_pos Ln]
        have ka := (keep n Ln).1
        have expandB : (s.cnt + 1) * B n = s.cnt * B n + B n := by rw [Nat.add_mul, Nat.one_mul]
        by_cases nx : L (n + 1) = 0
        · -- the run stopped at 138 zeros
          have full : s.cnt + 1 = 138 := by
            have stop : ¬ (s.cnt + 1 < 138) := by
              intro lt
              apply cont
              rw [mx138, z, nx]
              exact ⟨lt, rfl⟩
            omega
          have c := run.2 full
          have d1 : (if 0 < n + 1 ∧ L n = 0 ∧ L (n + 1) ≠ 0 then A (n + 1) else 0) = 0 := by
            rw [if_neg (by intro h; exact h.2.2 nx)]
          rw [d1]
          omega
        · have c := run.1
          have d1 : (if 0 < n + 1 ∧ L n = 0 ∧ L (n + 1) ≠ 0 then A (n + 1) else 0) = A n := by
            rw [if_pos ⟨by omega, Ln, nx⟩, ka]
          rw [d1]
          omega
      · -- a run of a nonzero length
        have Ln : L n ≠ 0 := by rw [← nextEq]; exact z
        have run := run_cost_nonzero wt P A B ch s.next s.prev (s.cnt + 1) s.mn z (by rw [nextEq]; exact smallN) (by
          intro enough
          rcases nzShape z with ⟨_, mn3, eq⟩ | ⟨_, mn4, ne⟩
          · exact ⟨by omega, fun diff => absurd eq diff⟩
          · exact ⟨by omega, fun _ => by omega⟩)
        rw [nextEq] at run
        rw [nextEq]
        rw [if_neg Ln] at prevBound
        rw [if_neg Ln]
        have expandP : (s.cnt + 1) * P (L n) = s.cnt * P (L n) + P (L n) := by rw [Nat.add_mul, Nat.one_mul]
        have d1 : (if 0 < n + 1 ∧ L n = 0 ∧ L (n + 1) ≠ 0 then A (n + 1) else 0) = 0 := by
          rw [if_neg (by intro h; exact Ln h.2.1)]
        have dle : (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) ≤ A n := by split <;> omega
        rw [d1]
        omega

/-- **The scan cost with region charges**: at most the charges of the first `n` entries plus one
credit `A n`. -/
theorem scan_cost_region (L wt P A B : Nat → Nat) (ch : ScanCharges wt P A B)
    (hL : ∀ n, L n < 2 ^ 16) (keep : ∀ i, L i = 0 → A (i + 1) = A i ∧ B (i + 1) = B i) (n : Nat)
    (small : ∀ i, i < n → L i ≤ 15) :
    mass (fun k => scanFreqUpTo L n k * wt k) 19 ≤ mass (regionCharge L P A B) n + A n := by
  have := scan_cost_region_pending L wt P A B ch hL keep n small
  have dle : (if 0 < n ∧ L (n - 1) = 0 ∧ L n ≠ 0 then A n else 0) ≤ A n := by split <;> omega
  omega

end Zlib.Trees.Proofs.Out
