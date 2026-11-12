import ZlibF.Proof.«trees.c.universal-overlay-costs»
import ZlibF.Math.DeflateOverlayCertificate

/-!
# trees.c: the cost of `scan_tree`'s bit-length symbols under a reference code, per entry

The memLevel 2 overlay certificate bounds the header under a fixed reference bit-length code `κ0`
(`refLen`). Here the cost of the bit-length symbols that `scan_tree` counts for a length sequence,
each at its reference length plus its extra bits, is bounded entry by entry: a nonzero length `x`
costs at most `max(κ0[x], 3)`, a zero costs at most 2 (`entryCost`).

Per run: a short run is `cnt` copies of its length; `REP_3_6` (`κ0[16] + 2 = 9` bits) covers at
least three entries, or four with the first copy; `REPZ_3_10` (6 bits) at least three zeros;
`REPZ_11_138` (14 bits) at least eleven. The runs are summed with the pending run as credit.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass mass_add mass_congr mass_zero)
open ZlibF.Math.DeflateOverlayCertificate (refLen entryCost)
set_option autoImplicit false

/-- The cost of bit-length symbol `k` under `κ0`, extra bits included. -/
def refWeight (k : Nat) : Nat := refLen k + blExtraBits k

theorem refLen_small (x : Nat) (small : x ≤ 15) : refLen x ≤ entryCost x ∧ blExtraBits x = 0 := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [refLen, entryCost, blExtraBits] <;> omega

theorem entryCost_three (x : Nat) (nz : x ≠ 0) : 3 ≤ entryCost x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
    simp [entryCost] at nz ⊢

/-- **One run** costs at most its count times the entry cost of its length. -/
theorem run_cost_le (cur : Nat) (prev : Int) (cnt mn : Nat) (small : cur ≤ 15)
    (shape : mn ≤ cnt → 3 ≤ cnt ∧ (cur ≠ 0 → (cur : Int) ≠ prev → 4 ≤ cnt)) :
    mass (fun k => runFreq (some (cur, prev, cnt, mn)) k * refWeight k) 19 ≤ cnt * entryCost cur := by
  have point : ∀ (c a : Nat), c < 19 → ∀ (g : Nat → Nat), (∀ k, g k = if k = c then a else 0) →
      mass (fun k => g k * refWeight k) 19 = a * refWeight c := by
    intro c a hc g hg
    rw [mass_congr (g := fun k => (if k = c then a else 0) * refWeight k) (fun k _ => by rw [hg k])]
    exact mass_point refWeight c a 19 hc
  have ⟨refC, extraC⟩ := refLen_small cur small
  by_cases few : cnt < mn
  · rw [point cur cnt (by omega) _ (fun k => by simp [runFreq, few])]
    simp only [refWeight, extraC, Nat.add_zero]
    exact Nat.mul_le_mul_left _ refC
  have ⟨three, four⟩ := shape (by omega)
  by_cases nz : cur ≠ 0
  · have e3 := entryCost_three cur nz
    by_cases newLen : (cur : Int) ≠ prev
    · have f4 := four nz newLen
      have split : mass (fun k => runFreq (some (cur, prev, cnt, mn)) k * refWeight k) 19 =
          mass (fun k => (if k = cur then 1 else 0) * refWeight k) 19 +
            mass (fun k => (if k = 16 then 1 else 0) * refWeight k) 19 := by
        rw [← mass_add]
        apply mass_congr
        intro k _
        simp only [runFreq, few, if_false, nz, newLen, ne_eq, not_false_eq_true, if_true, true_and]
        rw [Nat.add_mul]
      rw [split, mass_point refWeight cur 1 19 (by omega), mass_point refWeight 16 1 19 (by omega)]
      have w16 : refWeight 16 = 9 := by decide
      have wc : refWeight cur = refLen cur := by simp only [refWeight, extraC, Nat.add_zero]
      rw [w16, wc, Nat.one_mul, Nat.one_mul]
      have : cnt * entryCost cur ≥ 4 * entryCost cur := Nat.mul_le_mul_right _ f4
      omega
    · have same : (cur : Int) = prev := by simpa using newLen
      rw [point 16 1 (by omega) _ (fun k => by simp [runFreq, few, nz, same])]
      have w16 : refWeight 16 = 9 := by decide
      rw [w16]
      have : cnt * entryCost cur ≥ 3 * 3 := Nat.mul_le_mul three e3
      omega
  · have z : cur = 0 := by simpa using nz
    subst z
    have e0 : entryCost 0 = 2 := rfl
    by_cases ten : cnt ≤ 10
    · rw [point 17 1 (by omega) _ (fun k => by simp [runFreq, few, ten])]
      have w17 : refWeight 17 = 6 := by decide
      rw [w17, e0]
      omega
    · rw [point 18 1 (by omega) _ (fun k => by simp [runFreq, few, ten])]
      have w18 : refWeight 18 = 14 := by decide
      rw [w18, e0]
      omega

/-- **The scan, entry by entry**: the bit-length symbols of the first `n` iterations of
`scan_tree`, at their reference cost, plus the pending run at its entry cost, cost at most the
entry costs of the first `n` lengths. -/
theorem scan_cost_pending (L : Nat → Nat) (hL : ∀ n, L n < 2 ^ 16) (n : Nat)
    (small : ∀ i, i < n → L i ≤ 15) :
    mass (fun k => scanFreqUpTo L n k * refWeight k) 19 + (runAt L n).cnt * entryCost (L n) ≤
      mass (fun i => entryCost (L i)) n := by
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
    have rhs : mass (fun i => entryCost (L i)) (n + 1) = mass (fun i => entryCost (L i)) n + entryCost (L n) := rfl
    have lhs : mass (fun k => scanFreqUpTo L (n + 1) k * refWeight k) 19 =
        mass (fun k => scanFreqUpTo L n k * refWeight k) 19 +
          mass (fun k => runFreq (runStep L n (runAt L n)).2 k * refWeight k) 19 :=
      mass_mul_add _ _ _ 19
    have stepEq : runAt L (n + 1) = (runStep L n (runAt L n)).1 := rfl
    rw [rhs, lhs, stepEq]
    generalize runAt L n = s at prevBound inv nextEq ⊢
    obtain ⟨_, zeroShape, nzShape, _, _⟩ := inv
    have expand : (s.cnt + 1) * entryCost (L n) = s.cnt * entryCost (L n) + entryCost (L n) := by
      rw [Nat.add_mul, Nat.one_mul]
    unfold runStep
    dsimp only
    split
    · -- the run goes on: no cost, one more pending entry of the same length
      rename_i cont
      obtain ⟨_, sameNext⟩ := cont
      have none : mass (fun k => runFreq none k * refWeight k) 19 = 0 := by
        simp only [runFreq, Nat.zero_mul]; exact mass_zero 19
      dsimp only
      rw [none, ← sameNext, nextEq]
      omega
    · -- the run ends at n: its cost is at most its count times the entry cost
      have run := run_cost_le s.next s.prev (s.cnt + 1) s.mn (by rw [nextEq]; exact smallN) (by
        intro enough
        by_cases zero : s.next = 0
        · have := (zeroShape zero).2
          omega
        · rcases nzShape zero with ⟨_, mn3, eq⟩ | ⟨_, mn4, ne⟩
          · exact ⟨by omega, fun _ diff => absurd eq diff⟩
          · exact ⟨by omega, fun _ _ => by omega⟩)
      rw [nextEq] at run
      split <;> (try split) <;> dsimp only <;> rw [nextEq] <;> simp only [Nat.zero_mul, Nat.add_zero] <;> omega

/-- **The scan cost** of the first `n` iterations is at most the entry costs. -/
theorem scan_cost_le (L : Nat → Nat) (hL : ∀ n, L n < 2 ^ 16) (n : Nat) (small : ∀ i, i < n → L i ≤ 15) :
    mass (fun k => scanFreqUpTo L n k * refWeight k) 19 ≤ mass (fun i => entryCost (L i)) n := by
  have := scan_cost_pending L hL n small
  omega

end Zlib.Trees.Proofs.Out
