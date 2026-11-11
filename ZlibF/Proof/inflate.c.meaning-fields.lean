import ZlibF.Proof.«inflate.c.meaning-bits»

/-!
# inflate.c: header and trailer fields read through the bit buffer

Heap-free. A header or trailer mode pulls whole bytes into `hold` with
`NEEDBITS` and compares `hold` with an expected value. The held bits are the
bytes least significant first (`heldValue_bytesToBits`), and the comparisons
with the gzip length, the CRC-32 and the zlib Adler-32 are comparisons of the
bytes with `le32` and `be32` (`le32_of_value`, `be32_of_swap`).
-/

namespace Zlib.Inflate.Proofs.MeaningFields
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Proofs.MeaningBits ZlibF.Spec
set_option autoImplicit false

/-- The little-endian value of bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * leValue rest

theorem heldValue_append (x y : List Bool) :
    heldValue (x ++ y) = heldValue x + 2 ^ x.length * heldValue y := by
  induction x with
  | nil => simp [heldValue]
  | cons b t ih =>
    rw [List.cons_append, heldValue_cons, heldValue_cons, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ t.length), Nat.add_assoc]

theorem heldValue_byteBits (b : UInt8) : heldValue (byteBits b) = b.toNat := by
  have := natBits_heldValue (byteBits b)
  have lengthEq : (byteBits b).length = 8 := by simp [byteBits]
  rw [lengthEq] at this
  have bits : byteBits b = natBits 8 b.toNat := by
    rw [natBits_testBit]
    rfl
  rw [bits, heldValue_natBits, Nat.mod_eq_of_lt (by have := b.toNat_lt; simpa using this)]

theorem heldValue_bytesToBits : ∀ bs : List UInt8, heldValue (bytesToBits bs) = leValue bs
  | [] => by simp [heldValue, bytesToBits, leValue]
  | b :: rest => by
    have split : bytesToBits (b :: rest) = byteBits b ++ bytesToBits rest := by simp [bytesToBits]
    have lengthEq : (byteBits b).length = 8 := by simp [byteBits]
    rw [split, heldValue_append, heldValue_byteBits, heldValue_bytesToBits rest, lengthEq]
    simp only [leValue, show (2 : Nat) ^ 8 = 256 from rfl]

/-- Four bytes whose little-endian value is `n % 2^32` are `le32 n`. -/
theorem le32_of_value {a b c d : UInt8} {n : Nat} (value : leValue [a, b, c, d] = n % 2 ^ 32) :
    [a, b, c, d] = le32 n := by
  simp only [leValue] at value
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [le32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp <;> omega

/-- Conversely, the value of `le32 n` is `n % 2^32`. -/
theorem leValue_le32 (n : Nat) : leValue (le32 n) = n % 2 ^ 32 := by
  simp [le32, leValue]
  omega

#print axioms heldValue_bytesToBits
#print axioms le32_of_value

end Zlib.Inflate.Proofs.MeaningFields
