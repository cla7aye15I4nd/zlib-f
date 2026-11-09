import ZlibF.Math.InflateStoredEndian
import ZlibF.Proof.«inffast.c.sig»
import ZlibF.Spec.Format.Bits

namespace Zlib.Uncompr.Proof.StoredEndian
open C Zlib.Inflate ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

def packed (a b c d : UInt8) : UInt64 :=
  UInt64.ofNat (a.toNat + (b.toNat + (c.toNat + d.toNat * 256) * 256) * 256)

private theorem pair_bound (a b top : Nat) (low : a < 256) (high : b < top) :
    a + b * 256 < top * 256 := by omega

private theorem pair_low (a b : Nat) (low : a < 256) : (a+b*256)%256 = a := by
  simpa [Nat.mod_eq_of_lt low] using Nat.add_mul_mod_self_right a b 256

private theorem pair_high (a b : Nat) (low : a < 256) : (a+b*256)/256 = b := by
  rw [Nat.add_mul_div_right a b (by decide : 0 < 256),Nat.div_eq_of_lt low]
  simp

theorem packed_small (a b c d : UInt8) :
    a.toNat + (b.toNat + (c.toNat + d.toNat*256)*256)*256 < 2^32 := by
  have cd := pair_bound c.toNat d.toNat 256 c.toNat_lt d.toNat_lt
  have bcd := pair_bound b.toNat _ 65536 b.toNat_lt cd
  exact pair_bound a.toNat _ 16777216 a.toNat_lt bcd

/-- Four actual low-first pulled bytes swap back to their high-first word. -/
theorem swap_packed (a b c d : UInt8) :
    (ZSWAP32 (packed a b c d)).toNat =
      d.toNat + c.toNat*256 + b.toNat*65536 + a.toNat*16777216 := by
  let W := a.toNat + (b.toNat + (c.toNat+d.toNat*256)*256)*256
  have small : W < 2^32 := packed_small a b c d
  have small64 : W < 2^64 := Nat.lt_trans small (by decide)
  have value : (packed a b c d).toNat = W := by
    exact UInt64.toNat_ofNat_of_lt' small64
  have one : W / 256 = b.toNat + (c.toNat+d.toNat*256)*256 := pair_high _ _ a.toNat_lt
  have two : W / 65536 = c.toNat+d.toNat*256 := by
    change W / (256*256) = _
    rw [←Nat.div_div_eq_div_mul,one,pair_high _ _ b.toNat_lt]
  have three : W / 16777216 = d.toNat := by
    change W / (65536*256) = _
    rw [←Nat.div_div_eq_div_mul,two,pair_high _ _ c.toNat_lt]
  have low : W % 256 = a.toNat := pair_low _ _ a.toNat_lt
  rw [swap_value _ (by rw [value];exact small),value,three,two,one,low,
    pair_low _ _ c.toNat_lt,pair_low _ _ b.toNat_lt]

/-- Bytewise decomposition with the exact high-to-low word order. -/
theorem word_decompose (n : Nat) :
    n%256 + n/256%256*256 + n/65536%256*65536 + n/16777216*16777216 = n := by
  have step (a : Nat) : a = a%256 + a/256*256 := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div a 256).symm
  have high := congrArg (fun x => x*65536) (step (n/65536))
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.div_div_eq_div_mul,Nat.reduceMul] at high
  have middle := congrArg (fun x => x*256) (step (n/256))
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.div_div_eq_div_mul,Nat.reduceMul] at middle
  calc
    _ = n%256 + (n/256%256*256 + (n/65536%256*65536 + n/16777216*16777216)) := by ac_rfl
    _ = n%256 + (n/256%256*256 + n/65536*65536) := by rw [←high]
    _ = n%256 + n/256*256 := by rw [←middle]
    _ = n := (step n).symm

/-- The four RFC big-endian bytes recover the same original 32-bit value
through the actual machine swap. No enumeration of values is used. -/
theorem swap_be32 (v : UInt32) :
    ZSWAP32 (packed
      (UInt8.ofNat (v.toNat/16777216%256)) (UInt8.ofNat (v.toNat/65536%256))
      (UInt8.ofNat (v.toNat/256%256)) (UInt8.ofNat (v.toNat%256))) = v.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [swap_packed]
  simp only [UInt8.toNat_ofNat',show 2^8=256 by rfl,Nat.mod_mod,UInt32.toNat_toUInt64]
  have high : v.toNat/16777216 < 256 := by have := v.toNat_lt;omega
  rw [Nat.mod_eq_of_lt high]
  exact word_decompose v.toNat

private theorem low_bits (a b : Nat) (low : a < 256) :
    Zlib.Inflate.Proofs.natBits 8 (a+b*256) = Zlib.Inflate.Proofs.natBits 8 a := by
  calc
    _ = Zlib.Inflate.Proofs.natBits 8 ((a+b*256)%256) :=
      (Zlib.Inflate.Proofs.natBits_mod 8 (a+b*256)).symm
    _ = _ := congrArg (Zlib.Inflate.Proofs.natBits 8) (pair_low a b low)

/-- The same packed word has precisely the bitstream obtained by the four
actual byte pulls. This uses the runtime decoder's own low-bit sequence. -/
theorem packed_bits (a b c d : UInt8) :
    Zlib.Inflate.Proofs.natBits 32 (packed a b c d).toNat =
      Zlib.Inflate.Proofs.bytesBits [a,b,c,d] := by
  have small64 : a.toNat + (b.toNat+(c.toNat+d.toNat*256)*256)*256 < 2^64 :=
    Nat.lt_trans (packed_small a b c d) (by decide)
  rw [show (packed a b c d).toNat = a.toNat + (b.toNat+(c.toNat+d.toNat*256)*256)*256 from
    UInt64.toNat_ofNat_of_lt' small64]
  rw [Zlib.Inflate.Proofs.natBits_add 8 24,low_bits _ _ a.toNat_lt]
  simp only [show 2^8=256 from rfl,pair_high _ _ a.toNat_lt]
  rw [Zlib.Inflate.Proofs.natBits_add 8 16,low_bits _ _ b.toNat_lt]
  simp only [show 2^8=256 from rfl,pair_high _ _ b.toNat_lt]
  rw [Zlib.Inflate.Proofs.natBits_add 8 8,low_bits _ _ c.toNat_lt]
  simp only [show 2^8=256 from rfl,pair_high _ _ c.toNat_lt]
  simp [Zlib.Inflate.Proofs.bytesBits,Zlib.Inflate.Proofs.bytesBits_cons,List.append_assoc]

/-- A normalized held word is uniquely determined by its low bitstream. -/
theorem held_bits_unique (width x y : Nat) (left : x < 2^width) (right : y < 2^width)
    (bits : Zlib.Inflate.Proofs.natBits width x = Zlib.Inflate.Proofs.natBits width y) : x = y := by
  have read (v : Nat) (bound : v < 2^width) :
      readBits width (Zlib.Inflate.Proofs.natBits width v) = some (v,[]) := by
    have actual := Zlib.Inffast.Proofs.readBits_bitsOfNat width width v [] (Nat.le_refl _)
    simpa [Zlib.Inflate.Proofs.natBits_testBit,Zlib.Inffast.Proofs.bitsOfNat,Nat.mod_eq_of_lt bound] using actual
  have l := read x left
  have r := read y right
  rw [bits] at l
  exact congrArg Prod.fst (Option.some.inj (l.symm.trans r))

#print axioms swap_packed
#print axioms swap_be32
#print axioms packed_bits
#print axioms held_bits_unique
end Zlib.Uncompr.Proof.StoredEndian
