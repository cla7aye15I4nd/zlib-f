import ZlibF.Runtime.LibcStrings

/-! Decimal errno messages contain no embedded NUL byte. -/
namespace C.LibcStrings.Proofs
set_option autoImplicit false

private theorem decimal_digit_nonzero (n : Nat) (hn : n < 10) :
    (0 : UInt8) ∉ ([Nat.digitChar n].utf8Encode).data.toList := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- The actual decimal digit recursion cannot insert a NUL into its accumulator. -/
theorem decimal_digits_nonzero (fuel n : Nat) (ds : List Char)
    (nonzero : (0 : UInt8) ∉ ds.utf8Encode.data.toList) :
    (0 : UInt8) ∉ (Nat.toDigitsCore 10 fuel n ds).utf8Encode.data.toList := by
  induction fuel generalizing n ds with
  | zero => simpa [Nat.toDigitsCore] using nonzero
  | succ fuel ih =>
    have digit := decimal_digit_nonzero (n % 10) (Nat.mod_lt n (by decide))
    have cons : (0 : UInt8) ∉
        (Nat.digitChar (n % 10) :: ds).utf8Encode.data.toList := by
      rw [List.utf8Encode_cons, ByteArray.data_append, Array.toList_append]
      simpa only [List.mem_append, not_or] using And.intro digit nonzero
    rw [Nat.toDigitsCore]
    split
    · exact cons
    · exact ih (n / 10) _ cons

/-- Every signed decimal integer has NUL-free UTF-8 text, including its sign. -/
theorem integer_decimal_nonzero (z : Int) :
    (0 : UInt8) ∉ (toString z).toUTF8.data.toList := by
  change (0 : UInt8) ∉ (Int.repr z).toByteArray.data.toList
  cases z with
  | ofNat n =>
    simpa [Int.repr, Nat.repr, Nat.toDigits] using
      decimal_digits_nonzero (n + 1) n [] (by simp)
  | negSucc n =>
    have digits := decimal_digits_nonzero (n + 1 + 1) (n + 1) [] (by simp)
    simp only [Int.repr, Nat.repr, Nat.toDigits, String.toByteArray_append,
      ByteArray.data_append, Array.toList_append, String.toByteArray_ofList,
      List.mem_append, not_or]
    exact ⟨by decide, digits⟩

/-- The unchanged fixed-locale external message is a genuine C string prefix. -/
theorem errno_text_nonzero (e : Int32) :
    (0 : UInt8) ∉ (libcErrnoText e).toUTF8.data.toList := by
  unfold libcErrnoText
  repeat' split
  all_goals first
    | decide
    | change (0 : UInt8) ∉
        ("Unknown error " ++ toString e.toInt).toByteArray.data.toList
      rw [String.toByteArray_append, ByteArray.data_append, Array.toList_append]
      simpa only [List.mem_append, not_or, String.toUTF8_eq_toByteArray] using
        And.intro (by decide : (0 : UInt8) ∉ "Unknown error ".toByteArray.data.toList)
          (integer_decimal_nonzero e.toInt)

#print axioms decimal_digits_nonzero
#print axioms integer_decimal_nonzero
#print axioms errno_text_nonzero
end C.LibcStrings.Proofs
