import Std

namespace ZlibF.Math.CounterAccounting
set_option autoImplicit false

/-- A bounded 32-bit remaining count gives an exact 64-bit difference. -/
theorem difference_cast (base remaining : UInt32) (bound : remaining.toNat ≤ base.toNat) :
    (base - remaining).toUInt64 + remaining.toUInt64 = base.toUInt64 := by
  have numeric : (base - remaining).toNat + remaining.toNat = base.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound), Nat.sub_add_cancel bound]
  have words := congrArg UInt64.ofNat numeric
  simpa only [UInt64.ofNat_add, UInt64.ofNat_uInt32ToNat] using words

/-- Charging a produced prefix and rebasing to the remaining count
conserves the total-plus-base ledger, even when the 64-bit total wraps. -/
theorem charge_rebase (total : UInt64) (base remaining : UInt32)
    (bound : remaining.toNat ≤ base.toNat) :
    total + (base - remaining).toUInt64 + remaining.toUInt64 = total + base.toUInt64 := by
  rw [UInt64.add_assoc, difference_cast base remaining bound]

/-- A conserved ledger and exact public remaining count determine the
final wrapping total. No upper bound on the lifetime total is required. -/
theorem charge_from_ledger (before current : UInt64) (base remaining original : UInt32) (produced : Nat)
    (bound : remaining.toNat ≤ base.toNat)
    (counts : remaining.toNat + produced = original.toNat)
    (ledger : current + base.toUInt64 = before + original.toUInt64) :
    current + (base - remaining).toUInt64 = before + UInt64.ofNat produced := by
  have words := congrArg UInt64.ofNat counts
  simp only [UInt64.ofNat_add, UInt64.ofNat_uInt32ToNat] at words
  have combined : current + (base - remaining).toUInt64 + remaining.toUInt64 =
      (before + UInt64.ofNat produced) + remaining.toUInt64 := by
    rw [charge_rebase current base remaining bound, ledger, ← words]
    rw [UInt64.add_comm remaining.toUInt64, ← UInt64.add_assoc]
  have canceled := congrArg (fun value : UInt64 => value - remaining.toUInt64) combined
  simpa only [UInt64.add_sub_cancel] using canceled

end ZlibF.Math.CounterAccounting
