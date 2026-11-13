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
noncomputable def leValue : List UInt8 → Nat
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

theorem land_ff00 (x : Nat) : x &&& 0xff00 = (x / 256 % 256) * 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  rw [show (x / 256 % 256) * 256 = (x / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 from rfl, Nat.testBit_mul_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases lo : i < 8
  · have : (0xff00 : Nat).testBit i = false := (by decide : ∀ j < 8, (0xff00 : Nat).testBit j = false) i lo
    simp [this]
    omega
  · by_cases hi : i < 16
    · have : (0xff00 : Nat).testBit i = true := by
        have k : ∀ j < 8, (0xff00 : Nat).testBit (j + 8) = true := by decide
        have := k (i - 8) (by omega)
        rwa [show i - 8 + 8 = i by omega] at this
      rw [this, show i - 8 + 8 = i by omega]
      simp [show 8 ≤ i by omega, show i - 8 < 8 by omega]
    · have : (0xff00 : Nat).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (0xff00 : Nat) < 2 ^ 16)
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
      omega

theorem land_ff (x : Nat) : x &&& 0xff = x % 256 :=
  Nat.and_two_pow_sub_one_eq_mod x 8

/-- `ZSWAP32` of the little-endian word of four bytes is their big-endian word. -/
theorem zswap_value {hold : UInt64} {a b c d : UInt8}
    (value : hold.toNat = a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * (d.toNat + 256 * 0)))) :
    (ZSWAP32 hold).toNat = a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have q24 : hold.toNat / 2 ^ 24 = d.toNat := Nat.div_eq_of_lt_le (by omega) (by omega)
  have q8 : hold.toNat / 2 ^ 8 = b.toNat + 256 * c.toNat + 65536 * d.toNat :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  have q16 : (b.toNat + 256 * c.toNat + 65536 * d.toNat) / 256 = c.toNat + 256 * d.toNat :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simp only [ZSWAP32, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have c255 : (0xff : UInt64).toNat = 0xff := rfl
  have c65280 : (0xff00 : UInt64).toNat = 0xff00 := rfl
  have s24 : (24 : UInt64).toNat % 64 = 24 := rfl
  have s8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [c255, c65280, s24, s8, land_ff, land_ff, land_ff00, land_ff00, q24]
  rw [show hold.toNat / 2 ^ 8 = hold.toNat / 256 from rfl] at q8
  rw [q8, q16]
  rw [Nat.mod_eq_of_lt hd, show (c.toNat + 256 * d.toNat) % 256 = c.toNat by omega,
    show (b.toNat + 256 * c.toNat + 65536 * d.toNat) % 256 = b.toNat by omega,
    show hold.toNat % 256 = a.toNat by omega]
  rw [Nat.mod_eq_of_lt (show d.toNat + c.toNat * 256 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b.toNat * 256 * 2 ^ 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show d.toNat + c.toNat * 256 + b.toNat * 256 * 2 ^ 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a.toNat * 2 ^ 24 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show d.toNat + c.toNat * 256 + b.toNat * 256 * 2 ^ 8 + a.toNat * 2 ^ 24 < 2 ^ 64 by
      omega)]
  omega

/-- The held 32-bit word of four bytes equals a 32-bit value exactly when the
bytes are its little-endian encoding (the gzip CRC-32 check). -/
theorem hold_eq_le32 {hold : UInt64} {a b c d : UInt8} {v : UInt32}
    (value : hold.toNat = leValue [a, b, c, d]) :
    hold = v.toUInt64 ↔ [a, b, c, d] = le32 v.toNat := by
  constructor
  · intro eq
    apply le32_of_value
    rw [← value, eq, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt v.toNat_lt]
  · intro eq
    apply UInt64.toNat_inj.mp
    rw [value, eq, leValue_le32, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt v.toNat_lt]

/-- The byte-swapped held word of four bytes equals a 32-bit value exactly
when the bytes are its big-endian encoding (the zlib Adler-32 check). -/
theorem swap_eq_be32 {hold : UInt64} {a b c d : UInt8} {v : UInt32}
    (value : hold.toNat = leValue [a, b, c, d]) :
    ZSWAP32 hold = v.toUInt64 ↔ [a, b, c, d] = be32 v.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have hv := v.toNat_lt
  simp only [leValue] at value
  have swapped := zswap_value value
  constructor
  · intro eq
    have this := congrArg UInt64.toNat eq
    rw [swapped, UInt32.toNat_toUInt64] at this
    have d1 : v.toNat / 2 ^ 24 = a.toNat :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have d2 : v.toNat / 2 ^ 16 = a.toNat * 256 + b.toNat :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have d3 : v.toNat / 2 ^ 8 = a.toNat * 65536 + b.toNat * 256 + c.toNat :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have q1 : v.toNat / 2 ^ 24 % 256 = a.toNat := by rw [d1]; omega
    have q2 : v.toNat / 2 ^ 16 % 256 = b.toNat := by rw [d2]; omega
    have q3 : v.toNat / 2 ^ 8 % 256 = c.toNat := by rw [d3]; omega
    have q4 : v.toNat % 256 = d.toNat := by omega
    simp only [be32, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [q1, q2, q3, q4]
  · intro eq
    apply UInt64.toNat_inj.mp
    rw [swapped, UInt32.toNat_toUInt64]
    simp only [be32, List.cons.injEq, and_true] at eq
    obtain ⟨e1, e2, e3, e4⟩ := eq
    subst e1 e2 e3 e4
    simp
    omega

#print axioms hold_eq_le32
#print axioms swap_eq_be32

end Zlib.Inflate.Proofs.MeaningFields
