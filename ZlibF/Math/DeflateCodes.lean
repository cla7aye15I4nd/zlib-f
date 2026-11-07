import Std

/-!
# Canonical Huffman code assignment

The recurrence and symbol ordering follow RFC 1951 and the reference
`zlib-formal` proof of `gen_codes`. Values are unbounded natural numbers.
-/

namespace Zlib.Trees.Math

/-- First canonical code of each length. -/
def nextCode (bl : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => (nextCode bl b + bl b) * 2

/-- Number of earlier symbols with the selected length. -/
def countBefore (len : Nat → Nat) (l n : Nat) : Nat :=
  ((List.range n).filter (fun m => len m = l)).length

theorem countBefore_succ (len : Nat → Nat) (l n : Nat) :
    countBefore len l (n + 1) = countBefore len l n + (if len n = l then 1 else 0) := by
  unfold countBefore
  rw [List.range_succ, List.filter_append]
  by_cases h : len n = l <;> simp [h]

@[simp] theorem countBefore_zero (len : Nat → Nat) (l : Nat) : countBefore len l 0 = 0 := rfl

/-- Canonical code before reversal for transmission. -/
def canonicalCode (bl len : Nat → Nat) (n : Nat) : Nat :=
  nextCode bl (len n) + countBefore len (len n) n

/-- Reverse exactly the low `k` bits. -/
def reverseLowBits (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * reverseLowBits c k + (c / 2 ^ k) % 2

theorem reverseLowBits_mod (c k : Nat) :
    reverseLowBits (c % 2 ^ k) k = reverseLowBits c k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [reverseLowBits]
    have h1 : c % 2 ^ (k + 1) % 2 ^ k = c % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul_right_mod]
    have h2 : c % 2 ^ (k + 1) / 2 ^ k % 2 = c / 2 ^ k % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [← ih (c % 2 ^ (k + 1)), h1, ih, h2]

theorem reverseLowBits_mod_of_le (c k m : Nat) (hk : k ≤ m) :
    reverseLowBits (c % 2 ^ m) k = reverseLowBits c k := by
  rw [← reverseLowBits_mod (c % 2 ^ m) k, ← reverseLowBits_mod c k]
  congr 1
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  rw [Nat.pow_add, Nat.mod_mul_right_mod]

/-- Value stored by zlib for a symbol with positive length. -/
def storedCode (bl len : Nat → Nat) (n : Nat) : Nat :=
  reverseLowBits (canonicalCode bl len n) (len n)


/-- Reversing exactly k low bits produces a value that fits in k bits. -/
theorem reverseLowBits_lt (c k : Nat) : reverseLowBits c k < 2 ^ k := by
  induction k with
  | zero => simp only [reverseLowBits, Nat.pow_zero]; omega
  | succ k ih =>
    rw [reverseLowBits, Nat.pow_succ]
    have hb : c / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by omega)
    omega

/-- The value stored for a symbol fits its declared length. This bound
uses the low-bit reversal alone, and does not assume a valid code count. -/
theorem storedCode_lt (bl len : Nat → Nat) (n : Nat) : storedCode bl len n < 2 ^ len n :=
  reverseLowBits_lt _ _


/-- Bit i of the reversed value is bit k-1-i of the original value. -/
theorem reverseLowBits_testBit (c k i : Nat) (hi : i < k) :
    (reverseLowBits c k).testBit i = c.testBit (k - 1 - i) := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    have hb : c / 2 ^ k % 2 < 2 ^ 1 := by change c / 2 ^ k % 2 < 2; omega
    have hbit := Nat.testBit_two_pow_mul_add (reverseLowBits c k) hb i
    change (2 * reverseLowBits c k + c / 2 ^ k % 2).testBit i = _ at hbit
    rw [reverseLowBits, hbit]
    by_cases hi0 : i = 0
    · subst i
      rw [ite_eq_left (by omega), show k + 1 - 1 - 0 = k by omega]
      simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, Nat.mod_mod]
    · rw [ite_eq_right (by omega), ih (i - 1) (by omega)]
      congr 1
      omega

/-- Reading a reversed code least-significant bit first gives the original
code most-significant bit first. -/
theorem reverseLowBits_wire (c k : Nat) :
    (List.range k).map (fun i => (reverseLowBits c k).testBit i) =
      (List.range k).map (fun i => c.testBit (k - 1 - i)) := by
  apply List.map_congr_left
  intro i hi
  exact reverseLowBits_testBit c k i (List.mem_range.mp hi)

end Zlib.Trees.Math
