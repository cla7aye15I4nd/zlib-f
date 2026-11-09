import ZlibF.Proof.«inffast.c.sig»
import ZlibF.Spec.InflateDecodeTableShort

set_option autoImplicit false
namespace ZlibF.Math.InflateHeldBits
open ZlibF.Spec Zlib.Inffast.Proofs Zlib.Inftrees.Spec

/-- Extending the width of a normalized retained word appends only zero bits. -/
theorem extend_zero {value width : Nat} (normalized : value < 2 ^ width) (extra : Nat) :
    bitsOfNat value (width + extra) = bitsOfNat value width ++ List.replicate extra false := by
  unfold bitsOfNat
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  have high : value / 2 ^ width = 0 := Nat.div_eq_of_lt normalized
  have bits : ∀ index, value.testBit (width + index) = false := by
    intro index
    rw [Nat.add_comm width index, ← Nat.testBit_div_two_pow, high]
    simp
  simp only [Function.comp_def, bits]
  simp [List.map_const']

/-- A short retained word is queried with zero high bits. Mathematical
padding reconstructs exactly that root index, and supplies no input bits. -/
theorem padded_query {value width root : Nat} (normalized : value < 2 ^ width)
    (bounded : root ≤ 15) :
    ∃ suffix, readBits root (DecodeShort.padded (bitsOfNat value width)) =
      some (value % 2 ^ root, suffix) := by
  have padded : DecodeShort.padded (bitsOfNat value width) =
      bitsOfNat value (width + (15 - width)) := by
    rw [extend_zero normalized]
    simp only [DecodeShort.padded, bitsOfNat_length]
  rw [padded]
  have read := readBits_bitsOfNat root (width + (15 - width)) value [] (by omega)
  simp only [List.append_nil] at read
  exact ⟨_, read⟩

#print axioms extend_zero
#print axioms padded_query
end ZlibF.Math.InflateHeldBits
