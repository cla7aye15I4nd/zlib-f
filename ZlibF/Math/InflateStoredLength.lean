import ZlibF.Math.InflateStoredTrailer
import ZlibF.Spec.Format.Wrapper
import Init.Data.BitVec.Lemmas

namespace Zlib.Uncompr.Proof.StoredLength
open C ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

def word (n : Nat) : UInt64 := UInt64.ofNat (n+(65535-n)*65536)

theorem word_small (n : Nat) (small : n<65536) : n+(65535-n)*65536 < 2^32 := by omega

theorem packed_word (n : Nat) (small : n<65536) :
    StoredEndian.packed (UInt8.ofNat (n%256)) (UInt8.ofNat (n/256%256))
      (UInt8.ofNat ((65535-n)%256)) (UInt8.ofNat ((65535-n)/256%256)) = word n := by
  have high : n/256<256 := by omega
  have compHigh : (65535-n)/256<256 := by omega
  apply UInt64.toNat_inj.mp
  rw [show (word n).toNat=n+(65535-n)*65536 from
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (word_small n small) (by decide))]
  unfold StoredEndian.packed
  rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (StoredEndian.packed_small ..) (by decide))]
  simp only [UInt8.toNat_ofNat',show 2^8=256 by rfl,Nat.mod_mod,
    Nat.mod_eq_of_lt high,Nat.mod_eq_of_lt compHigh]
  have a := Nat.mod_add_div n 256
  have b := Nat.mod_add_div (65535-n) 256
  omega

theorem word_bits (n : Nat) (small : n<65536) :
    Zlib.Inflate.Proofs.natBits 32 (word n).toNat =
      Zlib.Inflate.Proofs.bytesBits (le16 n++le16 (65535-n)) := by
  rw [←packed_word n small]
  exact StoredEndian.packed_bits ..

theorem word_low (n : Nat) (small : n<65536) : (word n &&& 65535)=UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and]
  change (word n).toNat &&& (2^16-1)=(UInt64.ofNat n).toNat
  rw [Nat.and_two_pow_sub_one_eq_mod,
    show (word n).toNat=n+(65535-n)*65536 from
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (word_small n small) (by decide)),
    UInt64.toNat_ofNat_of_lt' (by change n<18446744073709551616;omega)]
  change (n+(65535-n)*65536)%65536=n
  omega

theorem word_high (n : Nat) (small : n<65536) : word n >>> 16=UInt64.ofNat (65535-n) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight,Nat.shiftRight_eq_div_pow]
  change (word n).toNat / 65536=(UInt64.ofNat (65535-n)).toNat
  rw [show (word n).toNat=n+(65535-n)*65536 from
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (word_small n small) (by decide)),
    UInt64.toNat_ofNat_of_lt' (by change 65535-n<18446744073709551616;omega)]
  omega

theorem complement (n : Nat) (small : n<65536) : (65535-n) ^^^ 65535=n := by
  have inverse := BitVec.toNat_not (x := BitVec.ofNat 16 n)
  simp only [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,BitVec.toNat_ofNat,
    show 2^16=65536 by rfl,Nat.mod_eq_of_lt small] at inverse
  change 65535 ^^^ n=65535-n at inverse
  rw [←inverse,Nat.xor_comm 65535 n,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem word_complement (n : Nat) (small : n<65536) :
    word n &&& (65535:UInt64)=(word n >>> 16) ^^^ (65535:UInt64) := by
  rw [word_low n small,word_high n small]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor]
  rw [UInt64.toNat_ofNat_of_lt' (by change n<18446744073709551616;omega),
    UInt64.toNat_ofNat_of_lt' (by change 65535-n<18446744073709551616;omega)]
  change n=(65535-n) ^^^ 65535
  exact (complement n small).symm

theorem word_length (n : Nat) (small : n<65536) :
    (word n).toUInt32 &&& 65535=UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and,UInt64.toNat_toUInt32]
  change ((word n).toNat%2^32) &&& (2^16-1)=(UInt32.ofNat n).toNat
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_mod_of_dvd _ (by decide : 2^16 ∣ 2^32)]
  rw [show (word n).toNat=n+(65535-n)*65536 from
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (word_small n small) (by decide)),
    UInt32.toNat_ofNat_of_lt' (by change n<4294967296;omega)]
  change (n+(65535-n)*65536)%65536=n
  omega

#print axioms word_bits
#print axioms word_complement
#print axioms word_length
end Zlib.Uncompr.Proof.StoredLength
