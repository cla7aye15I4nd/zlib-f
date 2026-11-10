import ZlibF.Proof.«inflate.c.whole-dictionary-ready-call-cut»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

theorem header_guard_arithmetic {cmf flg : UInt8} {s : InflateState} {l : IL}
    (wrap : s.wrap = 5) (word : l.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    headHeaderRejected s l = decide ((cmf.toNat * 256 + flg.toNat) % 31 ≠ 0) ∧
    headMethodRejected l = decide (cmf.toNat % 16 ≠ 8) ∧
    (headWindowRegs l).len.toNat = cmf.toNat / 16 + 8 := by
  have cb := cmf.toNat_lt
  have fb := flg.toNat_lt
  have heldBound : l.hold.toNat < 65536 := by omega
  have low8 : l.hold.toUInt32 &&& 255 = UInt32.ofNat cmf.toNat := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt32.toNat_ofNat]
    change l.hold.toNat % 4294967296 &&& (2^8-1) = cmf.toNat % 4294967296
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have high8 : (l.hold >>> 8).toNat = flg.toNat := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    change l.hold.toNat / 256 = flg.toNat
    omega
  have low4 : l.hold.toUInt32 &&& 15 = UInt32.ofNat (cmf.toNat % 16) := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt32.toNat_ofNat]
    change l.hold.toNat % 4294967296 &&& (2^4-1) = cmf.toNat % 16 % 4294967296
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have window : ((l.hold >>> (4 : UInt32).toUInt64).toUInt32 &&& 15).toNat = cmf.toNat / 16 := by
    simp only [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
    change (l.hold.toNat / 16) % 4294967296 &&& (2^4-1) = cmf.toNat / 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  constructor
  · simp only [headHeaderRejected, wrap, show (((5 : Int32) &&& 1) == 0) = false from rfl,
      Bool.false_or, show ((1 : UInt32) <<< 8 - 1) = 255 from rfl, low8]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    change (¬ _ = (0 : UInt64)) ↔ _
    rw [← UInt64.toNat_inj]
    simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_shiftLeft,
      UInt32.toNat_ofNat, UInt64.toNat_ofNat, high8, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow]
    change ((cmf.toNat % 4294967296 * 256 % 4294967296 + flg.toNat) % 18446744073709551616) % 31 ≠ 0 ↔ _
    rw [Nat.mod_eq_of_lt (by omega : cmf.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : cmf.toNat * 256 < 4294967296),
      Nat.mod_eq_of_lt (by omega : cmf.toNat * 256 + flg.toNat < 18446744073709551616)]
  constructor
  · simp only [headMethodRejected, show ((1 : UInt32) <<< 4 - 1) = 15 from rfl, low4]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    change (¬ _ = (8 : UInt32)) ↔ _
    rw [← UInt32.toNat_inj]
    change cmf.toNat % 16 % 4294967296 ≠ 8 ↔ _
    omega
  · change (((l.hold >>> (4 : UInt32).toUInt64).toUInt32 &&& 15) + 8).toNat = _
    rw [UInt32.toNat_add, window]
    change (cmf.toNat / 16 + 8) % 4294967296 = _
    omega

#print axioms header_guard_arithmetic
end Zlib.Inflate.Proofs.WholeWrapper
