import ZlibF.Proof.«inflate.c.main.bits»

namespace Zlib.Uncompr.Proof.StoredEndian
open C Zlib.Inflate
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem mask_byte1 (n : Nat) : n &&& 65280 = (n / 256 % 256) * 256 := by
  have low : (n &&& 65280) % 256 = 0 := by
    change (n &&& 65280) % 2^8 = 0
    rw [Nat.and_mod_two_pow]
    simp
  have high : (n &&& 65280) / 256 = n / 256 % 256 := by
    change (n &&& 65280) / 2^8 = n / 256 % 256
    rw [Nat.and_div_two_pow]
    change n/256 &&& 255 = n/256%256
    exact Nat.and_two_pow_sub_one_eq_mod _ 8
  have division := Nat.div_add_mod (n &&& 65280) 256
  rw [high,low] at division
  omega

/-- The translated swap selects exactly the four low bytes. -/
theorem swap_value (q : UInt64) (small : q.toNat < 2^32) :
    (ZSWAP32 q).toNat = q.toNat / 16777216 + (q.toNat / 65536 % 256) * 256 +
      (q.toNat / 256 % 256) * 65536 + (q.toNat % 256) * 16777216 := by
  have mask8 (n : Nat) : n &&& 255 = n%256 := Nat.and_two_pow_sub_one_eq_mod n 8
  unfold ZSWAP32
  simp only [UInt64.toNat_add,UInt64.toNat_and,UInt64.toNat_shiftRight,UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat,UInt64.toNat_ofNat',Nat.reduceMod,Nat.reducePow,Nat.reduceMul,Nat.reduceDiv]
  simp only [Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,mask8,mask_byte1]
  simp only [Nat.reduceMod,Nat.reducePow,Nat.reduceMul,Nat.reduceDiv]
  simp only [Nat.div_div_eq_div_mul,Nat.mul_assoc,Nat.reduceMul]
  have b0 : q.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have b1 : q.toNat / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have b2 : q.toNat / 65536 % 256 < 256 := Nat.mod_lt _ (by decide)
  have top : q.toNat / 16777216 < 256 := by omega
  rw [Nat.mod_eq_of_lt top]
  have firstSmall := Nat.add_lt_add top (Nat.mul_lt_mul_of_pos_right b2 (by decide : 0 < 256))
  have secondSmall := Nat.mul_lt_mul_of_pos_right b1 (by decide : 0 < 65536)
  have bothSmall := Nat.add_lt_add firstSmall secondSmall
  have lastSmall := Nat.mul_lt_mul_of_pos_right b0 (by decide : 0 < 16777216)
  have allSmall := Nat.add_lt_add bothSmall lastSmall
  have first : q.toNat / 16777216 + q.toNat / 65536 % 256 * 256 < 18446744073709551616 :=
    Nat.lt_trans firstSmall (by decide)
  have second : q.toNat / 256 % 256 * 65536 < 18446744073709551616 :=
    Nat.lt_trans secondSmall (by decide)
  have both : q.toNat / 16777216 + q.toNat / 65536 % 256 * 256 + q.toNat / 256 % 256 * 65536 < 18446744073709551616 :=
    Nat.lt_trans bothSmall (by decide)
  have last : q.toNat % 256 * 16777216 < 18446744073709551616 :=
    Nat.lt_trans lastSmall (by decide)
  have all : q.toNat / 16777216 + q.toNat / 65536 % 256 * 256 + q.toNat / 256 % 256 * 65536 + q.toNat % 256 * 16777216 < 18446744073709551616 :=
    Nat.lt_trans allSmall (by decide)
  rw [Nat.mod_eq_of_lt first,Nat.mod_eq_of_lt second,Nat.mod_eq_of_lt both,
    Nat.mod_eq_of_lt last,Nat.mod_eq_of_lt all]

#print axioms swap_value
end Zlib.Uncompr.Proof.StoredEndian
