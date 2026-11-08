import Std
import ZlibF.Math.DeflateTreeScan
import ZlibF.Proof.«trees.c.heap.gbmath»

/-! # Forced-leaf cancellation in exact Huffman costs

The two-leaf argument is adapted from CostForce in the pinned zlib-formal
reference 0f1428677ebf5b1614ff77f4702bbb382b2bf3c6. Its proof bodies are
retained. The pointwise-frequency version below uses the current actual
repair trace rather than the reference heap or forceIter representation.
No theorem here alone establishes a translated constructor contract.
-/

namespace ZlibF.Math.HuffmanCost
open Zlib.Trees.Proofs.GB
set_option autoImplicit false

theorem pow_sub_le_half {L x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ L) : 2 ^ (L - x) ≤ 2 ^ (L - 1) :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem two_leaves {L x y : Nat} (hx1 : 1 ≤ x) (hxL : x ≤ L) (hy1 : 1 ≤ y) (hyL : y ≤ L)
    (h : 2 ^ (L - x) + 2 ^ (L - y) = 2 ^ L) : x = 1 ∧ y = 1 := by
  have a := pow_sub_le_half hx1 hxL
  have b := pow_sub_le_half hy1 hyL
  have e : 2 ^ L = 2 ^ (L - 1) + 2 ^ (L - 1) := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; omega
  have ha : 2 ^ (L - x) = 2 ^ (L - 1) := by omega
  have hb : 2 ^ (L - y) = 2 ^ (L - 1) := by omega
  have px : ¬ L - x < L - 1 := fun h => by have := Nat.pow_lt_pow_right (by decide : 1 < 2) h; omega
  have py : ¬ L - y < L - 1 := fun h => by have := Nat.pow_lt_pow_right (by decide : 1 < 2) h; omega
  omega

/-- In a complete code with exactly two nonzero lengths, both are `1`. -/
theorem len_one_of_two {len : Nat → Nat} {N L : Nat} (hL : ∀ n, len n ≤ L)
    (hk : rs (fun n => if len n ≠ 0 then 2 ^ (L - len n) else 0) N = 2 ^ L)
    (h2 : rs (fun n => if len n ≠ 0 then 1 else 0) N = 2) :
    ∀ n, n < N → len n ≠ 0 → len n = 1 := by
  intro n hn hne
  have hL1 : 1 ≤ L := by have := hL n; omega
  have hTU : ∀ i, (if len i ≠ 0 then 2 ^ (L - len i) else 0) ≤ (if len i ≠ 0 then 2 ^ (L - 1) else 0) := by
    intro i
    by_cases e : len i ≠ 0
    · rw [if_pos e, if_pos e]; exact pow_sub_le_half (by omega) (hL i)
    · rw [if_neg e, if_neg e]; exact Nat.le_refl 0
  have hU : rs (fun i => if len i ≠ 0 then 2 ^ (L - 1) else 0) N = 2 ^ L := by
    rw [rs_congr (G := fun i => 2 ^ (L - 1) * (if len i ≠ 0 then 1 else 0)) (fun i _ => by
      by_cases e : len i ≠ 0
      · rw [if_pos e, if_pos e, Nat.mul_one]
      · rw [if_neg e, if_neg e, Nat.mul_zero]), rs_mul, h2]
    rw [show L = (L - 1) + 1 by omega, Nat.pow_succ]; simp only [Nat.add_sub_cancel]
  have hsum := rs_add (fun i => if len i ≠ 0 then 2 ^ (L - len i) else 0)
    (fun i => (if len i ≠ 0 then 2 ^ (L - 1) else 0) - (if len i ≠ 0 then 2 ^ (L - len i) else 0)) N
  rw [rs_congr (G := fun i => if len i ≠ 0 then 2 ^ (L - 1) else 0) (fun i _ => by
    have := hTU i; omega), hU, hk] at hsum
  have h0 := rs_zero_of (show rs (fun i => (if len i ≠ 0 then 2 ^ (L - 1) else 0) -
    (if len i ≠ 0 then 2 ^ (L - len i) else 0)) N = 0 by omega) n hn
  simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte] at h0
  have : ¬ L - len n < L - 1 := fun h => by have := Nat.pow_lt_pow_right (by decide : 1 < 2) h; omega
  have := hL n
  omega


/-- Only lengths inside the source alphabet require a bound. Unused work
array entries outside it may retain arbitrary integer values. -/
theorem len_one_of_two_within {len : Nat → Nat} {N L : Nat}
    (bound : ∀ n, n < N → len n ≤ L)
    (kraft : rs (fun n => if len n ≠ 0 then 2 ^ (L - len n) else 0) N = 2 ^ L)
    (count : rs (fun n => if len n ≠ 0 then 1 else 0) N = 2) :
    ∀ n, n < N → len n ≠ 0 → len n = 1 := by
  let clipped := fun n => if n < N then len n else 0
  have clippedBound : ∀ n, clipped n ≤ L := by
    intro n
    by_cases fit : n < N
    · simpa only [clipped, if_pos fit] using bound n fit
    · simp [clipped, fit]
  have clippedKraft : rs (fun n => if clipped n ≠ 0 then 2 ^ (L - clipped n) else 0) N = 2 ^ L := by
    rw [rs_congr (G := fun n => if len n ≠ 0 then 2 ^ (L - len n) else 0)
      (fun n fit => by simp only [clipped, if_pos fit])]
    exact kraft
  have clippedCount : rs (fun n => if clipped n ≠ 0 then 1 else 0) N = 2 := by
    rw [rs_congr (G := fun n => if len n ≠ 0 then 1 else 0)
      (fun n fit => by simp only [clipped, if_pos fit])]
    exact count
  intro n fit nonzero
  have one := len_one_of_two clippedBound clippedKraft clippedCount n fit
  simpa only [clipped, if_pos fit] using one (by simpa only [clipped, if_pos fit] using nonzero)

/-- Fresh frequency-one dummy leaves contribute exactly the source
repair count. When any repair occurs, the complete code has two leaves
and both lengths are one. Dummy symbols carry no extra bits. -/
theorem forced_dynamic_cost (original prepared length extra : Nat → Nat) (N L k : Nat)
    (point : ∀ n, n < N → prepared n = original n ∨
      original n = 0 ∧ prepared n = 1 ∧ n ≤ 2)
    (counts : rs (fun n => if prepared n ≠ 0 then 1 else 0) N =
      rs (fun n => if original n ≠ 0 then 1 else 0) N + k)
    (two : k ≠ 0 → rs (fun n => if prepared n ≠ 0 then 1 else 0) N = 2)
    (bound : ∀ n, n < N → length n ≤ L)
    (used : ∀ n, n < N → (length n ≠ 0 ↔ prepared n ≠ 0))
    (kraft : rs (fun n => if length n ≠ 0 then 2 ^ (L - length n) else 0) N = 2 ^ L)
    (extraZero : ∀ n, n ≤ 2 → extra n = 0) :
    rs (fun n => prepared n * (length n + extra n)) N =
      rs (fun n => original n * (length n + extra n)) N + k := by
  have countSplit : rs (fun n => if prepared n ≠ 0 then 1 else 0) N =
      rs (fun n => if original n ≠ 0 then 1 else 0) N +
        rs (fun n => if original n = 0 ∧ prepared n ≠ 0 then 1 else 0) N := by
    rw [← rs_add]
    apply rs_congr
    intro n fit
    rcases point n fit with same | ⟨zero, one, _small⟩
    · rw [same]
      by_cases empty : original n = 0 <;> simp [empty]
    · simp [zero, one]
  have forcedCount : rs (fun n => if original n = 0 ∧ prepared n ≠ 0 then 1 else 0) N = k := by omega
  have lengthCount : rs (fun n => if length n ≠ 0 then 1 else 0) N =
      rs (fun n => if prepared n ≠ 0 then 1 else 0) N :=
    rs_congr (fun n fit => by simp only [used n fit])
  have dummyLength : rs (fun n => if original n = 0 ∧ prepared n ≠ 0 then length n else 0) N = k := by
    rw [← forcedCount]
    apply rs_congr
    intro n fit
    by_cases dummy : original n = 0 ∧ prepared n ≠ 0
    · rw [if_pos dummy, if_pos dummy]
      by_cases zero : k = 0
      · have absent := rs_zero_of (forcedCount.trans zero) n fit
        simp [dummy] at absent
      · exact len_one_of_two_within bound kraft (lengthCount.trans (two zero)) n fit ((used n fit).mpr dummy.2)
    · rw [if_neg dummy, if_neg dummy]
  calc
    _ = rs (fun n => original n * (length n + extra n) +
        if original n = 0 ∧ prepared n ≠ 0 then length n else 0) N := by
      apply rs_congr
      intro n fit
      rcases point n fit with same | ⟨zero, one, small⟩
      · rw [same]
        by_cases empty : original n = 0 <;> simp [empty]
      · simp [zero, one, extraZero n small]
    _ = _ := by rw [rs_add, dummyLength]

/-- The source scan count is the finite sum of positive-frequency
indicators used by the exact-cost argument. -/
theorem scanCount_eq_rs (fr : Nat → UInt16) (N : Nat) :
    Zlib.Trees.Math.scanCount fr N = rs (fun n => if (fr n).toNat ≠ 0 then 1 else 0) N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [Zlib.Trees.Math.scanCount, rs_succ, ih]
    by_cases zero : fr n = 0
    · simp [zero]
    · have nonzero : (fr n).toNat ≠ 0 := by
        intro h
        exact zero (UInt16.toNat_inj.mp h)
      simp [zero, nonzero]

end ZlibF.Math.HuffmanCost
