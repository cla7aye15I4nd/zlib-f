import Init.Data.Nat.Mod

namespace ZlibF.Math.InflateLookup

/-- Masking a combined prefix and suffix, then dropping the prefix, selects
exactly the suffix bits. -/
theorem slice_eq (value dropped width : Nat) :
    value % 2 ^ (dropped + width) / 2 ^ dropped = value / 2 ^ dropped % 2 ^ width := by
  rw [Nat.pow_add, Nat.mod_mul_right_div_self]

/-- The suffix index is bounded even when the source holds fewer bits. -/
theorem slice_lt (value dropped width : Nat) :
    value % 2 ^ (dropped + width) / 2 ^ dropped < 2 ^ width := by
  rw [slice_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A zero high nibble forces both flag bits tested by the fast decoder to zero. -/
theorem high_zero_flags (op : UInt8) (high : op &&& 240 = 0) :
    op &&& 16 = 0 ∧ op &&& 64 = 0 := by
  constructor
  · calc
      op &&& 16 = (op &&& 240) &&& 16 := by rw [UInt8.and_assoc]; rfl
      _ = 0 := by rw [high]; rfl
  · calc
      op &&& 64 = (op &&& 240) &&& 64 := by rw [UInt8.and_assoc]; rfl
      _ = 0 := by rw [high]; rfl

/-- Link widths occupy only the low nibble. -/
theorem small_high_zero (op : UInt8) (bound : op.toNat ≤ 15) : op &&& 240 = 0 := by
  have low : op &&& 15 = op := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_and]
    change op.toNat &&& (2 ^ 4 - 1) = op.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  calc
    op &&& 240 = (op &&& 15) &&& 240 := by rw [low]
    _ = 0 := by rw [UInt8.and_assoc, show (15 : UInt8) &&& 240 = 0 from rfl, UInt8.and_zero]

end ZlibF.Math.InflateLookup
