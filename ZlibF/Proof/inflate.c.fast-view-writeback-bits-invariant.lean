import ZlibF.Proof.«inflate.c.fast-view-prelude-ready-invariant»

namespace Zlib.Inflate.Proofs
open C
set_option autoImplicit false

/-- Returning whole bytes from any `UInt32` bit count leaves its exact
remainder modulo eight. This needs no bound from the broken loop branch. -/
theorem fast_writeback_residual_bits (bits : UInt32) :
    (bits - ((bits >>> 3) <<< 3)).toNat = bits.toNat % 8 := by
  have whole := Zlib.Inffast.Proofs.bits_whole bits
  have shifted : ((bits >>> 3) <<< 3).toNat =
      bits.toNat / 8 * 8 := by
    rw [UInt32.toNat_shiftLeft, whole, Nat.shiftLeft_eq]
    change (bits.toNat / 8 * 8) % 4294967296 =
      bits.toNat / 8 * 8
    exact Nat.mod_eq_of_lt (by
      have width := UInt32.toNat_lt bits
      omega)
  have within : ((bits >>> 3) <<< 3).toNat ≤ bits.toNat := by
    rw [shifted]
    omega
  rw [Zlib.Inffast.Proofs.u32_toNat_sub within, shifted]
  omega

/-- The translated writeback's checked shift is safe on every possible
loop result, including an error `break`. -/
theorem fast_writeback_shift_ok (bits : UInt32) :
    Zlib.Inffast.shl32 1
      (bits - ((bits >>> 3) <<< 3)) =
    pure ((1 : UInt32) <<<
      (bits - ((bits >>> 3) <<< 3))) := by
  apply Zlib.Inffast.Proofs.shl32_eq
  rw [fast_writeback_residual_bits]
  omega

end Zlib.Inflate.Proofs
