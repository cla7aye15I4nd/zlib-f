import Std

namespace ZlibF.Math.BitBuffer
set_option autoImplicit false

/-- Appending a bounded word above normalized low bits retains normalization.
The bound also proves that neither the shifted word nor the sum wraps. -/
theorem append_normalized (hold word : UInt64) (bits : UInt32) (extra : Nat)
    (held : hold.toNat < 2 ^ bits.toNat) (wordBound : word.toNat < 2 ^ extra)
    (shift : bits.toNat < 64) (fit : bits.toNat + extra ≤ 64) :
    (hold + (word <<< bits.toUInt64)).toNat < 2 ^ (bits.toNat + extra) := by
  have budget := Nat.mul_le_mul_right (2 ^ bits.toNat) (Nat.succ_le_of_lt wordBound)
  rw [Nat.succ_mul] at budget
  have sumBound : hold.toNat + word.toNat * 2 ^ bits.toNat < 2 ^ (extra + bits.toNat) := by
    rw [Nat.pow_add]
    omega
  have powerBound := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show extra + bits.toNat ≤ 64 by omega)
  have totalBound : hold.toNat + word.toNat * 2 ^ bits.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le sumBound powerBound
  have shiftBound : word.toNat * 2 ^ bits.toNat < 2 ^ 64 := by omega
  have shifted : (word <<< bits.toUInt64).toNat = word.toNat * 2 ^ bits.toNat := by
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt shift,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt shiftBound]
  rw [UInt64.toNat_add, shifted, Nat.mod_eq_of_lt totalBound, Nat.add_comm bits.toNat extra]
  exact sumBound

end ZlibF.Math.BitBuffer
