import ZlibF.Proof.«inflate.c.base»
import ZlibF.Spec.Format

/-!
# inflate.c: bit-list algebra and the shift lemmas of the bit buffer

Heap-free. `natBits k n` is the low `k` bits of `n`, least significant first; `bytesBits` is the DEFLATE bit sequence of a byte
list (RFC 1951, 3.1.1). `bytesBits_eq_bytesToBits` ties it to the format specification `ZlibF.Spec.bytesToBits`.
The shift lemmas say when `<<<` and `>>>` of the translation are the arithmetic they look like.
-/

namespace Zlib.Inflate.Proofs

/-- The low `k` bits of `n`, least significant first. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: natBits k (n / 2)

/-- Bytes as a DEFLATE bit stream (each byte least significant bit first). -/
def bytesBits (bs : List UInt8) : List Bool := bs.flatMap fun b => natBits 8 b.toNat

theorem natBits_length : ∀ k n, (natBits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [natBits, natBits_length k]

theorem natBits_add : ∀ k m n, natBits (k + m) n = natBits k n ++ natBits m (n / 2 ^ k)
  | 0, m, n => by simp [natBits]
  | k + 1, m, n => by
    rw [show k + 1 + m = (k + m) + 1 by omega]
    simp only [natBits, natBits_add k m (n / 2), List.cons_append, Nat.div_div_eq_div_mul,
      Nat.pow_succ]
    rw [Nat.mul_comm 2 (2 ^ k)]

theorem natBits_mod : ∀ k n, natBits k (n % 2 ^ k) = natBits k n
  | 0, _ => rfl
  | k + 1, n => by
    simp only [natBits]
    have h1 : n % 2 ^ (k + 1) % 2 = n % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have h2 : n % 2 ^ (k + 1) / 2 = (n / 2) % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [h1, h2, natBits_mod k]

theorem natBits_take (k n j : Nat) (hj : j ≤ k) : (natBits k n).take j = natBits j n := by
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  rw [natBits_add, List.take_append_of_le_length (by simp [natBits_length])]
  exact List.take_of_length_le (by simp [natBits_length])

theorem natBits_drop (k n j : Nat) (hj : j ≤ k) :
    (natBits k n).drop j = natBits (k - j) (n / 2 ^ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  rw [natBits_add, List.drop_append_of_le_length (by simp [natBits_length])]
  simp [natBits_length]

/-- `hold += b << bits; bits += 8` appends the byte's bits. -/
theorem natBits_pull (bits hold b : Nat) (hh : hold < 2 ^ bits) (hb : b < 256) :
    natBits (bits + 8) (hold + b * 2 ^ bits) = natBits bits hold ++ natBits 8 b := by
  rw [natBits_add]
  have h1 : natBits bits (hold + b * 2 ^ bits) = natBits bits hold := by
    rw [← natBits_mod bits (hold + b * 2 ^ bits), ← natBits_mod bits hold]
    congr 1
    rw [Nat.add_mul_mod_self_right]
  have h2 : (hold + b * 2 ^ bits) / 2 ^ bits = b := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos bits), Nat.div_eq_of_lt hh, Nat.zero_add]
  rw [h1, h2]

theorem bytesBits_nil : bytesBits [] = [] := rfl

theorem bytesBits_cons (b : UInt8) (bs : List UInt8) :
    bytesBits (b :: bs) = natBits 8 b.toNat ++ bytesBits bs := by
  simp [bytesBits]

theorem bytesBits_append (xs ys : List UInt8) :
    bytesBits (xs ++ ys) = bytesBits xs ++ bytesBits ys := by
  simp [bytesBits]

theorem bytesBits_length (bs : List UInt8) : (bytesBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [bytesBits_cons]; simp [natBits_length, ih]; omega

theorem bytesBits_drop (bs : List UInt8) (j : Nat) :
    (bytesBits bs).drop (8 * j) = bytesBits (bs.drop j) := by
  induction bs generalizing j with
  | nil => simp [bytesBits]
  | cons b bs ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [bytesBits_cons, show 8 * (j + 1) = 8 + 8 * j by omega, ← List.drop_drop,
        List.drop_append_of_le_length (by simp [natBits_length]),
        List.drop_eq_nil_of_le (as := natBits 8 b.toNat) (by simp [natBits_length]),
        List.nil_append, ih]
      simp

theorem natBits_testBit : ∀ k n, natBits k n = (List.range k).map fun i => n.testBit i
  | 0, _ => rfl
  | k + 1, n => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, natBits, natBits_testBit k (n / 2)]
    congr 1
    · by_cases h : n % 2 = 1 <;> simp [Nat.testBit_zero, h]
    · apply List.map_congr_left
      intro i _
      simp [Function.comp, Nat.testBit_succ]

/-- `bytesBits` is the bit sequence of the format specification. -/
theorem bytesBits_eq_bytesToBits (bs : List UInt8) : ZlibF.Spec.bytesToBits bs = bytesBits bs := by
  unfold ZlibF.Spec.bytesToBits bytesBits
  congr 1; funext b
  rw [natBits_testBit]
  rfl

/-! ## The shifts of the bit buffer -/

open C Zlib.Inflate

theorem shl32_run (x n : UInt32) (hn : n.toNat < 32) : shl32 x n = pure (x <<< n) := by
  have : n < 32 := UInt32.lt_iff_toNat_lt.mpr (by simpa using hn)
  simp [shl32, this]

theorem shr32_run (x n : UInt32) (hn : n.toNat < 32) : shr32 x n = pure (x >>> n) := by
  have : n < 32 := UInt32.lt_iff_toNat_lt.mpr (by simpa using hn)
  simp [shr32, this]

theorem shl64_run (x : UInt64) (n : UInt32) (hn : n.toNat < 64) : shl64 x n = pure (x <<< n.toUInt64) := by
  have : n < 64 := UInt32.lt_iff_toNat_lt.mpr (by simpa using hn)
  simp [shl64, this]

theorem shr64_run (x : UInt64) (n : UInt32) (hn : n.toNat < 64) : shr64 x n = pure (x >>> n.toUInt64) := by
  have : n < 64 := UInt32.lt_iff_toNat_lt.mpr (by simpa using hn)
  simp [shr64, this]

theorem shr64_toNat (x : UInt64) (n : UInt32) (hn : n.toNat < 64) :
    (x >>> n.toUInt64).toNat = x.toNat / 2 ^ n.toNat := by
  rw [UInt64.toNat_shiftRight]
  simp only [UInt32.toNat_toUInt64]
  rw [Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem shl64_toNat (x : UInt64) (n : UInt32) (hn : n.toNat < 64)
    (hx : x.toNat * 2 ^ n.toNat < 2 ^ 64) :
    (x <<< n.toUInt64).toNat = x.toNat * 2 ^ n.toNat := by
  rw [UInt64.toNat_shiftLeft]
  simp only [UInt32.toNat_toUInt64]
  rw [Nat.mod_eq_of_lt hn, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hx

theorem shl32_one_toNat (n : UInt32) (hn : n.toNat < 32) : ((1 : UInt32) <<< n).toNat = 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftLeft]
  simp only [UInt32.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : n.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (by
    calc 2 ^ n.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hn
      _ = UInt32.size := rfl)

/-- `(1U << n) - 1` is the mask of `n` low bits. -/
theorem mask_toNat (n : UInt32) (hn : n.toNat < 32) : ((1 : UInt32) <<< n - 1).toNat = 2 ^ n.toNat - 1 := by
  have h := shl32_one_toNat n hn
  have hpos : 1 ≤ 2 ^ n.toNat := Nat.one_le_two_pow
  rw [UInt32.toNat_sub_of_le]
  · rw [h]; rfl
  · rw [UInt32.le_iff_toNat_le, h]; exact hpos

theorem land_mask32 (x : UInt32) (k : Nat) (m : UInt32) (hm : m.toNat = 2 ^ k - 1) :
    (x &&& m).toNat = x.toNat % 2 ^ k := by
  rw [UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

end Zlib.Inflate.Proofs
