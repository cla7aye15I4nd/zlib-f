import Init.Data.Int.Repr
import Init.Data.Char.Lemmas
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Decode
import Lean.Elab.Tactic.Omega

/-! # Decimal text as UTF-8 bytes

Decimal digits are ASCII. Their UTF-8 encoding is their character code, rather
than a distinct or assumed display representation.
-/

namespace ZlibF.Math.DecimalText

/-- The executable packed-byte conversion agrees with its mathematical data list. -/
theorem byteArray_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  have aux : ∀ k i acc, bytes.size - i = k →
      ByteArray.toList.loop bytes i acc = acc.reverse ++ bytes.data.toList.drop i := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro i acc hk
      rw [ByteArray.toList.loop]
      split
      · rename_i hi
        rw [ih (bytes.size - (i + 1)) (by omega) (i + 1) (bytes.get! i :: acc) rfl]
        have hli : i < bytes.data.toList.length := by simpa using hi
        rw [List.drop_eq_getElem_cons hli]
        simp [List.reverse_cons, List.append_assoc, ByteArray.get!, getElem!_pos bytes.data i (by simpa using hi)]
      · rename_i hi
        have hli : bytes.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hi
        simp [List.drop_eq_nil_of_le hli]
  simpa [ByteArray.toList] using aux bytes.size 0 [] (by simp)

/-- Executable packed-list conversion commutes with packed byte append. -/
theorem byteArray_toList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList, ByteArray.toList_data_append, ← byteArray_toList, ← byteArray_toList]

/-- Actual string append and UTF-8 conversion preserve concatenation. -/
theorem string_utf8_append (a b : String) :
    (a ++ b).toUTF8.toList = a.toUTF8.toList ++ b.toUTF8.toList := by
  simp only [String.toUTF8, String.toByteArray_append, byteArray_toList_append]

/-- The UTF-8 encoder emits one code byte for every decimal character. -/
theorem digit_encode (c : Char) (hc : c.isDigit) :
    String.utf8EncodeChar c = [c.toNat.toUInt8] := by
  have hd := Char.isDigit_iff_toNat.mp hc
  have hs : c.utf8Size = 1 := by
    simp [Char.utf8Size, UInt32.le_iff_toNat_le]
    simp at hd
    omega
  exact String.utf8EncodeChar_eq_singleton hs

/-- The actual UTF-8 bytes of a list of decimal digits. -/
theorem digits_utf8 (cs : List Char) (hc : ∀ c, c ∈ cs → c.isDigit) :
    (String.ofList cs).toUTF8.toList = cs.map (fun c => c.toNat.toUInt8) := by
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, byteArray_toList,
    List.toList_data_toByteArray]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, digit_encode c (hc c (by simp)), List.cons_append,
      List.nil_append, List.map_cons]
    rw [ih (fun d hd => hc d (by simp [hd]))]

/-- Nat's actual decimal toString text, encoded as bytes. -/
theorem nat_toString_utf8 (n : Nat) :
    (toString n).toUTF8.toList = (Nat.toDigits 10 n).map (fun c => c.toNat.toUInt8) := by
  rw [Nat.toString_eq_ofList_toDigits]
  exact digits_utf8 _ (fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-- The public signed integer display is exactly the nonnegative decimal text. -/
theorem int_nonnegative_toString_utf8 (z : Int) (hz : 0 ≤ z) :
    (toString z).toUTF8.toList = (Nat.toDigits 10 z.natAbs).map (fun c => c.toNat.toUInt8) := by
  cases z with
  | ofNat n => exact nat_toString_utf8 n
  | negSucc n => omega

#print axioms byteArray_toList
#print axioms string_utf8_append
#print axioms digit_encode
#print axioms digits_utf8
#print axioms nat_toString_utf8
#print axioms int_nonnegative_toString_utf8
end ZlibF.Math.DecimalText
