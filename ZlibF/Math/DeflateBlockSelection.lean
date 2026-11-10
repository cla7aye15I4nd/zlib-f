import Std

/-! # Byte-cost selection bounds the stored branch at default memory level -/

namespace ZlibF.Math.DeflateSelection
set_option autoImplicit false

def byteCost (bits : UInt64) : UInt64 := (bits + 3 + 7) >>> 3

def selectedCost (opt fixed : UInt64) (forceFixed : Bool) : UInt64 :=
  if fixed ≤ opt ∨ forceFixed = true then fixed else opt

theorem selected_le_fixed (opt fixed : UInt64) (forceFixed : Bool) :
    (selectedCost opt fixed forceFixed).toNat ≤ fixed.toNat := by
  unfold selectedCost
  split
  · exact Nat.le_refl _
  · rename_i no
    have less : ¬ fixed ≤ opt := fun yes => no (Or.inl yes)
    change ¬ fixed.toNat ≤ opt.toNat at less
    omega

/-- Rounding and shifting follow the exact unsigned source operations.
The original 31-bit symbol budget is small enough for both additions. -/
theorem byte_cost_default {bits : UInt64} {symbols : Nat}
    (count : symbols ≤ 16383) (budget : bits.toNat ≤ 31 * symbols + 7) :
    (byteCost bits).toNat ≤ 63486 := by
  have first : (bits + 3).toNat = bits.toNat + 3 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 < 18446744073709551616; omega)
  have second : (bits + 3 + 7).toNat = bits.toNat + 10 := by
    rw [UInt64.toNat_add, first]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 + 7 < 18446744073709551616; omega)
  unfold byteCost
  rw [UInt64.toNat_shiftRight, second]
  change (bits.toNat + 10) >>> 3 ≤ 63486
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- If the actual stored branch wins the comparison, its data and the
worst two-byte aligned tag plus four-byte length header fit the default
pending range. The explicit stored-word bound prevents wrapping the
comparison's `stored + 4`; caller position arithmetic must supply it. -/
theorem stored_default_room {bits opt stored : UInt64} {symbols : Nat} {forceFixed : Bool}
    (count : symbols ≤ 16383) (budget : bits.toNat ≤ 31 * symbols + 7)
    (storedWord : stored.toNat ≤ 4294967296)
    (selected : stored + 4 ≤ selectedCost opt (byteCost bits) forceFixed) :
    stored.toNat + 6 ≤ 63488 := by
  have fixedBound := byte_cost_default count budget
  have minBound := selected_le_fixed opt (byteCost bits) forceFixed
  have add : (stored + 4).toNat = stored.toNat + 4 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change stored.toNat + 4 < 18446744073709551616; omega)
  change (stored + 4).toNat ≤ (selectedCost opt (byteCost bits) forceFixed).toNat at selected
  rw [add] at selected
  omega

end ZlibF.Math.DeflateSelection
