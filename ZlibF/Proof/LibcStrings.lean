import ZlibF.Runtime.LibcStrings
import ZlibF.Runtime.Schema

namespace C.LibcStrings.Proofs
open C

private theorem digit_bytes (n : Nat) : (Nat.digitChar n).utf8Size = 1 := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ 15 < n := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
  all_goals first | rfl | simp [Nat.digitChar, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega]; rfl

private theorem cons_bytes (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).utf8ByteSize = c.utf8Size + (String.ofList cs).utf8ByteSize := by
  simp [String.ofList_cons]

/-- Coarse bit-based digit bound. No enumeration of Int32 values. -/
theorem digits_bytes_bound (k fuel n : Nat) (ds : List Char) (hn : n < 2 ^ k) :
    (String.ofList (Nat.toDigitsCore 10 fuel n ds)).utf8ByteSize ≤
      (String.ofList ds).utf8ByteSize + k + 1 := by
  induction k generalizing fuel n ds with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    cases fuel with
    | zero => simp [Nat.toDigitsCore]
    | succ f => simp [Nat.toDigitsCore, digit_bytes, Nat.add_comm]
  | succ k ih =>
    cases fuel with
    | zero => simp [Nat.toDigitsCore]; omega
    | succ fuel =>
      have hd : n / 10 < 2 ^ k := by
        rw [Nat.pow_succ] at hn
        omega
      rw [Nat.toDigitsCore]
      split
      · simp [digit_bytes]; omega
      · have hi := ih fuel (n / 10) (Nat.digitChar (n % 10) :: ds) hd
        rw [cons_bytes, digit_bytes] at hi
        omega

/-- Int32's decimal text, including a possible minus sign, uses ≤34 bytes. -/
theorem int32_decimal_bytes (e : Int32) : (toString e.toInt).utf8ByteSize ≤ 34 := by
  change (Int.repr e.toInt).utf8ByteSize ≤ 34
  have hlo := Int32.le_toInt e
  have hhi := Int32.toInt_lt e
  cases he : e.toInt with
  | ofNat n =>
    have hn : n < 2 ^ 32 := by
      rw [he] at hhi
      change (n : Int) < 2147483648 at hhi
      omega
    have hd := digits_bytes_bound 32 (n + 1) n [] hn
    simpa [Int.repr, Nat.repr, Nat.toDigits] using Nat.le_trans hd (by decide : 0 + 32 + 1 ≤ 34)
  | negSucc n =>
    have hn : n + 1 < 2 ^ 32 := by rw [he] at hlo; omega
    have hd := digits_bytes_bound 32 (n + 1 + 1) (n + 1) [] hn
    simp only [Int.repr, String.utf8ByteSize_append]
    change 1 + (String.ofList (Nat.toDigitsCore 10 (n + 1 + 1) (n + 1) [])).utf8ByteSize ≤ 34
    simp only [String.ofList_nil, String.utf8ByteSize_empty] at hd
    omega

/-- Every fixed external errno text plus its NUL fits strictly below64 bytes. -/
theorem errno_bytes_lt64 (e : Int32) : (strBytes (libcErrnoText e)).size < 64 := by
  have hd := int32_decimal_bytes e
  unfold libcErrnoText
  by_cases h0 : (e == 0) = true
  · rw [if_pos h0]; decide
  rw [if_neg h0]
  by_cases h2 : (e == 2) = true
  · rw [if_pos h2]; decide
  rw [if_neg h2]
  by_cases h4 : (e == 4) = true
  · rw [if_pos h4]; decide
  rw [if_neg h4]
  by_cases h5 : (e == 5) = true
  · rw [if_pos h5]; decide
  rw [if_neg h5]
  by_cases h9 : (e == 9) = true
  · rw [if_pos h9]; decide
  rw [if_neg h9]
  by_cases h11 : (e == 11) = true
  · rw [if_pos h11]; decide
  rw [if_neg h11]
  by_cases h13 : (e == 13) = true
  · rw [if_pos h13]; decide
  rw [if_neg h13]
  by_cases h17 : (e == 17) = true
  · rw [if_pos h17]; decide
  rw [if_neg h17]
  by_cases h21 : (e == 21) = true
  · rw [if_pos h21]; decide
  rw [if_neg h21]
  by_cases h22 : (e == 22) = true
  · rw [if_pos h22]; decide
  rw [if_neg h22]
  by_cases h27 : (e == 27) = true
  · rw [if_pos h27]; decide
  rw [if_neg h27]
  by_cases h28 : (e == 28) = true
  · rw [if_pos h28]; decide
  rw [if_neg h28]
  by_cases h29 : (e == 29) = true
  · rw [if_pos h29]; decide
  rw [if_neg h29]
  by_cases h75 : (e == 75) = true
  · rw [if_pos h75]; decide
  rw [if_neg h75]
  simp only [strBytes, Array.size_push, ByteArray.size_data]
  change ("Unknown error " ++ toString e.toInt).utf8ByteSize + 1 < 64
  rw [String.utf8ByteSize_append]
  change 14 + (toString e.toInt).utf8ByteSize + 1 < 64
  omega

#print axioms digits_bytes_bound
#print axioms int32_decimal_bytes
#print axioms errno_bytes_lt64
end C.LibcStrings.Proofs
