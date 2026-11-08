import Init.Data.UInt.Lemmas
import Init.Tactics

namespace ZlibF.Math.InflateOutputAccount
set_option autoImplicit false

/-- A wrapping total plus its saved segment base gives the exact produced
count after the suffix credit. No bound on cumulative stream length is used. -/
theorem suffix_credit {old current : UInt64} {base remaining original : UInt32} {made : Nat}
    (account : current + base.toUInt64 = old + original.toUInt64)
    (bounded : remaining.toNat ≤ base.toNat)
    (count : remaining.toNat + made = original.toNat) :
    current + (base - remaining).toUInt64 = old + UInt64.ofNat made := by
  have cast (value : UInt32) : value.toUInt64 = UInt64.ofNat value.toNat := by simp
  have credit : (current + (base - remaining).toUInt64) + remaining.toUInt64 = current + base.toUInt64 := by
    rw [UInt64.add_assoc, cast (base - remaining), cast remaining, ← UInt64.ofNat_add,
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bounded), Nat.sub_add_cancel bounded,
      ← cast base]
  have total : UInt64.ofNat made + remaining.toUInt64 = original.toUInt64 := by
    rw [cast remaining, ← UInt64.ofNat_add, cast original]
    congr 1
    omega
  apply (UInt64.add_left_inj remaining.toUInt64).mp
  calc
    (current + (base - remaining).toUInt64) + remaining.toUInt64 = current + base.toUInt64 := credit
    _ = old + original.toUInt64 := account
    _ = (old + UInt64.ofNat made) + remaining.toUInt64 := by rw [UInt64.add_assoc, total]

end ZlibF.Math.InflateOutputAccount
