import ZlibF.Math.DeflateHeader

/-! # Seven bits per source length bound the complete dynamic header -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

theorem codeBits_length (t : Nat → UInt16 × UInt16) (k : Nat) :
    (codeBits t k).length = (t k).2.toNat := by
  simp only [codeBits, natBits, List.length_map, List.length_range]

theorem repeated_bits_length {α : Type} (n : Nat) (bits : List α) :
    (List.replicate n bits).flatten.length = n * bits.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- A completed run costs no more than seven bits per represented source
length, including either repeat code and all of its extra bits. -/
theorem runBits_length_le_count (t : Nat → UInt16 × UInt16) (cur cnt mn : Nat) (prev : Int)
    (codes : ∀ k, k < 19 → (t k).2.toNat ≤ 7) (current : cur ≤ 15) (minimum : 3 ≤ mn) :
    (runBits t (some (cur, prev, cnt, mn))).length ≤ 7 * cnt := by
  have codeCur := codes cur (by omega)
  have code16 := codes 16 (by omega)
  have code17 := codes 17 (by omega)
  have code18 := codes 18 (by omega)
  simp only [runBits]
  split
  · rw [repeated_bits_length, codeBits_length]
    have := Nat.mul_le_mul_left cnt codeCur
    omega
  · rename_i long
    split
    · split <;> simp only [List.length_append, codeBits_length, natBits, List.length_map, List.length_range] <;> omega
    · split <;> simp only [List.length_append, codeBits_length, natBits, List.length_map, List.length_range] <;> omega

theorem runAt_minimum (L : Nat → Nat) (n : Nat) : 3 ≤ (runAt L n).mn := by
  induction n with
  | zero => simp only [runAt, runInit]; split <;> simp
  | succ n ih =>
    simp only [runAt, runStep]
    split
    · exact ih
    · split
      · simp
      · split <;> simp

/-- The pending run receives the same seven-bit credit as lengths already
emitted. No assumptions on the unused sentinel or later entries are used. -/
theorem treeBitsUpTo_length_budget (t : Nat → UInt16 × UInt16) (L : Nat → Nat) (n : Nat)
    (codes : ∀ k, k < 19 → (t k).2.toNat ≤ 7) (lengths : ∀ i, i < n → L i ≤ 15) :
    (treeBitsUpTo t L n).length + 7 * (runAt L n).cnt ≤ 7 * n := by
  induction n with
  | zero => simp only [treeBitsUpTo, runAt, runInit]; split <;> simp
  | succ n ih =>
    have previous := ih (fun i bound => lengths i (by omega))
    have current : (runAt L n).next ≤ 15 := by rw [runAt_next]; exact lengths n (by omega)
    have runBound := runBits_length_le_count t (runAt L n).next ((runAt L n).cnt + 1)
      (runAt L n).mn (runAt L n).prev codes current (runAt_minimum L n)
    simp only [treeBitsUpTo, List.length_append, runAt, runStep]
    split
    · simp only [runBits, List.length_nil, Nat.add_zero]
      omega
    · split
      · simp only [Nat.mul_zero, Nat.add_zero]
        omega
      · split <;> simp only [Nat.mul_zero, Nat.add_zero] <;> omega

theorem sendTreeBits_length_budget (t : Nat → UInt16 × UInt16) (L : Nat → Nat) (maxc : Nat)
    (codes : ∀ k, k < 19 → (t k).2.toNat ≤ 7) (lengths : ∀ i, i ≤ maxc → L i ≤ 15) :
    (sendTreeBits t L maxc).length ≤ 7 * (maxc + 1) := by
  have bound := treeBitsUpTo_length_budget t L (maxc + 1) codes (fun i fit => lengths i (by omega))
  unfold sendTreeBits
  omega

/-- This bound includes count fields, all transmitted BL lengths and both
source alphabets. Repeat codes do not require an additional margin. -/
theorem allTreesBits_length_budget (t : Nat → UInt16 × UInt16) (L D : Nat → Nat) (lc dc bc : Nat)
    (codes : ∀ k, k < 19 → (t k).2.toNat ≤ 7)
    (literal : ∀ i, i ≤ lc - 1 → L i ≤ 15) (distance : ∀ i, i ≤ dc - 1 → D i ≤ 15)
    (literalMin : 1 ≤ lc) (literalMax : lc ≤ 286)
    (distanceMin : 1 ≤ dc) (distanceMax : dc ≤ 30) (blMax : bc ≤ 19) :
    (allTreesBits t L D lc dc bc).length ≤ 2283 := by
  have lit := sendTreeBits_length_budget t L (lc - 1) codes literal
  have dist := sendTreeBits_length_budget t D (dc - 1) codes distance
  rw [allTreesBits_length]
  omega

end Zlib.Trees.Proofs.Out
