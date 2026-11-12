import ZlibF.Proof.«trees.c.runs»
import ZlibF.Math.DeflateSymbolMass
import ZlibF.Math.DeflateTreeWeight

/-!
# trees.c: `scan_tree` counts at most one bit-length symbol per entry

The first `n` iterations of `scan_tree` add at most `n` to the bit-length frequencies in total:
a finished run of `cnt` entries adds `cnt` copies of its length when it is short, and at most two
symbols (`16` with the length, or `17`, or `18`) when `cnt ≥ min_count ≥ 3`. So the bit-length
tree of a block weighs at most `286 + 30 = 316`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass mass_add mass_mono)
set_option autoImplicit false

theorem mass_point_le (n a v : Nat) : mass (fun j => if j = a then v else 0) n ≤ v := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    show mass _ n + (if n = a then v else 0) ≤ v
    by_cases e : n = a
    · subst e
      have zero : mass (fun j => if j = n then v else 0) n = 0 := by
        rw [ZlibF.Math.DeflateSymbols.mass_congr (g := fun _ => 0) fun k hk => by rw [ite_eq_right (by omega)]]
        exact ZlibF.Math.DeflateSymbols.mass_zero n
      rw [zero, ite_eq_left rfl]; omega
    · rw [ite_eq_right e]; omega

/-- One finished run adds at most its length, when `min_count ≥ 3`. -/
theorem runFreq_mass (cur : Nat) (prev : Int) (cnt mn : Nat) (three : 3 ≤ mn) :
    mass (runFreq (some (cur, prev, cnt, mn))) 19 ≤ cnt := by
  by_cases few : cnt < mn
  · have e : runFreq (some (cur, prev, cnt, mn)) = fun k => if k = cur then cnt else 0 := by
      funext k; simp [runFreq, few]
    rw [e]; exact mass_point_le 19 cur cnt
  · by_cases nz : cur ≠ 0
    · have le : ∀ k, k < 19 → runFreq (some (cur, prev, cnt, mn)) k ≤
          (fun j => if j = cur then 1 else 0) k + (fun j => if j = 16 then 1 else 0) k := by
        intro k _
        simp only [runFreq, few, nz, ite_false, ite_true, ne_eq, not_false_eq_true]
        by_cases a : (cur : Int) ≠ prev ∧ k = cur
        · rw [ite_eq_left a, ite_eq_left a.2]; exact Nat.le_refl _
        · rw [ite_eq_right a]; split <;> omega
      have := mass_mono le
      rw [mass_add] at this
      have := mass_point_le 19 cur 1
      have := mass_point_le 19 16 1
      omega
    · have z : cur = 0 := by omega
      by_cases ten : cnt ≤ 10
      · have e : runFreq (some (cur, prev, cnt, mn)) = fun k => if k = 17 then 1 else 0 := by
          funext k; simp [runFreq, few, z, ten]
        rw [e]; have := mass_point_le 19 17 1; omega
      · have e : runFreq (some (cur, prev, cnt, mn)) = fun k => if k = 18 then 1 else 0 := by
          funext k; simp [runFreq, few, z, ten]
        rw [e]; have := mass_point_le 19 18 1; omega

/-- **Scan count.** -/
theorem scan_count_le (L : Nat → Nat) : ∀ n,
    mass (scanFreqUpTo L n) 19 + (runAt L n).cnt ≤ n ∧ 3 ≤ (runAt L n).mn
  | 0 => by
    have z : mass (scanFreqUpTo L 0) 19 = 0 := ZlibF.Math.DeflateSymbols.mass_zero 19
    rw [z]
    simp only [runAt, runInit]
    split <;> simp
  | n + 1 => by
    obtain ⟨ih, three⟩ := scan_count_le L n
    have e : mass (scanFreqUpTo L (n + 1)) 19 =
        mass (scanFreqUpTo L n) 19 + mass (runFreq (runStep L n (runAt L n)).2) 19 :=
      mass_add (scanFreqUpTo L n) (runFreq (runStep L n (runAt L n)).2) 19
    rw [e]
    show _ + (runStep L n (runAt L n)).1.cnt ≤ n + 1 ∧ 3 ≤ (runStep L n (runAt L n)).1.mn
    generalize runAt L n = s at ih three
    unfold runStep
    simp only []
    split
    · have z : mass (runFreq none) 19 = 0 := ZlibF.Math.DeflateSymbols.mass_zero 19
      rw [z]
      exact ⟨by (try dsimp only); omega, three⟩
    · have r := runFreq_mass s.next s.prev (s.cnt + 1) s.mn three
      refine ⟨?_, ?_⟩
      · split
        · (try dsimp only); omega
        · split <;> ((try dsimp only); omega)
      · split
        · simp
        · split <;> simp

/-- The bit-length symbols of one tree: at most one per entry. -/
theorem scan_mass_le (L : Nat → Nat) (n : Nat) : mass (scanFreqUpTo L n) 19 ≤ n := by
  have := (scan_count_le L n).1; omega

end Zlib.Trees.Proofs.Out
