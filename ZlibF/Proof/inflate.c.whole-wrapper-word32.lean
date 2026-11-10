import ZlibF.Proof.«inflate.c.whole-wrapper-byte-source»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.FunctionalTrailerWire
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem swap_word32_bound (value : UInt64) : (ZSWAP32 value).toNat < 4294967296 := by
  have mask8 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
  have b0 := Nat.mod_lt value.toNat (by decide : 0 < 256)
  have b1 := Nat.mod_lt (value.toNat / 256) (by decide : 0 < 256)
  have b2 := Nat.mod_lt (value.toNat / 65536) (by decide : 0 < 256)
  have b3 := Nat.mod_lt (value.toNat / 16777216) (by decide : 0 < 256)
  have sum2 : value.toNat / 16777216 % 256 + value.toNat / 65536 % 256 * 256 < 18446744073709551616 := by omega
  have shift1 : value.toNat / 256 % 256 * 256 * 256 < 18446744073709551616 := by omega
  have shift0 : value.toNat % 256 * 16777216 < 18446744073709551616 := by omega
  have sum3 : value.toNat / 16777216 % 256 + value.toNat / 65536 % 256 * 256 + value.toNat / 256 % 256 * 256 * 256 < 18446744073709551616 := by omega
  have sum4 : value.toNat / 16777216 % 256 + value.toNat / 65536 % 256 * 256 + value.toNat / 256 % 256 * 256 * 256 + value.toNat % 256 * 16777216 < 18446744073709551616 := by omega
  simp only [ZSWAP32, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, mask8, wrapper_mask_middle_byte, Nat.reducePow, Nat.reduceMod,
    Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.mod_eq_of_lt sum2, Nat.mod_eq_of_lt shift1, Nat.mod_eq_of_lt shift0, Nat.mod_eq_of_lt sum3, Nat.mod_eq_of_lt sum4]
  omega

/-- A real full dictionary-id word determines its independent four bytes.
The identifier is computed from the actual swap, not supplied as a goal. -/
theorem actual_be32_word {regs : IL} (width : regs.bits.toNat = 32) :
    ∃ identifier : UInt32, ZSWAP32 regs.hold = identifier.toUInt64 ∧
      natBits regs.bits.toNat regs.hold.toNat = bytesBits (be32 identifier.toNat) := by
  let identifier := (ZSWAP32 regs.hold).toUInt32
  have bound := swap_word32_bound regs.hold
  have swap : ZSWAP32 regs.hold = identifier.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp only [identifier, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt bound]
  have wire := swap_be32_inverse swap
  have first := readBits_held_stream regs [] 32 (by omega)
  have dropped : (stream regs []).drop 32 = [] := by
    simp only [stream, bytesBits_nil, List.append_nil, width]
    exact List.drop_eq_nil_of_le (by rw [natBits_length]; omega)
  rw [dropped] at first
  have second := wrapper_readBits_be32 identifier.toNat []
  have firstRead : readBits 32 (natBits 32 regs.hold.toNat) = some
      (regs.hold.toNat % 4294967296, []) := by
    simpa only [dropped, stream, bytesBits_nil, List.append_nil, width, Nat.reducePow] using first
  rw [wire] at firstRead
  have secondRead : readBits 32 (bytesBits (be32 identifier.toNat)) = some
      (identifier.toNat / 16777216 % 256 + 256 * (identifier.toNat / 65536 % 256) +
        65536 * (identifier.toNat / 256 % 256) + 16777216 * (identifier.toNat % 256), []) := by
    simpa only [List.append_nil] using second
  have same := readBits_input_unique (by rw [natBits_length]; omega)
    (by simp only [bytesBits_length, be32, List.length_cons, List.length_nil]; decide) firstRead secondRead
  exact ⟨identifier, swap, by simpa only [width] using same⟩

#print axioms swap_word32_bound
#print axioms actual_be32_word
end Zlib.Inflate.Proofs.WholeWrapper
