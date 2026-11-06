import ZlibF.Proof.«inffast.c.match»
import ZlibF.Spec.Format

/-!
# inffast.c: the bit stream that the bit buffer and the input pointer stand for

`bitsOfNat H b` is the list of the low `b` bits of `H`, least significant first (the order in which the bits of the
buffer are consumed). `Sg e H b i` is the bit sequence of a state of `inflate_fast`: the `b` bits of the buffer `H`,
then the bits of the input bytes from offset `i` to the end of the input range. Reading a byte into the buffer, and
dropping bits, do not change the sequence (up to the dropped bits).
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

open ZlibF.Spec

/-- The low `b` bits of `H`, least significant first. -/
def bitsOfNat (H b : Nat) : List Bool := (List.range b).map fun j => H.testBit j

theorem bitsOfNat_length (H b : Nat) : (bitsOfNat H b).length = b := by simp [bitsOfNat]

theorem bitsOfNat_succ (H b : Nat) : bitsOfNat H (b + 1) = H.testBit 0 :: bitsOfNat (H / 2) b := by
  unfold bitsOfNat
  rw [List.range_succ_eq_map]
  simp [Function.comp_def, Nat.testBit_div_two]

theorem bitsOfNat_zero (H : Nat) : bitsOfNat H 0 = [] := rfl

theorem bitsOfNat_drop (H b k : Nat) (hk : k ≤ b) : bitsOfNat (H / 2 ^ k) (b - k) = (bitsOfNat H b).drop k := by
  apply List.ext_getElem
  · simp [bitsOfNat_length]
  · intro n h1 h2
    simp only [bitsOfNat, List.getElem_map, List.getElem_range, List.getElem_drop, Nat.testBit_div_two_pow]
    rw [Nat.add_comm]

theorem readBits_bitsOfNat : ∀ (x b H : Nat) (r : List Bool), x ≤ b →
    readBits x (bitsOfNat H b ++ r) = some (H % 2 ^ x, bitsOfNat (H / 2 ^ x) (b - x) ++ r)
  | 0, b, H, r, _ => by simp [readBits, Nat.mod_one]
  | x + 1, b, H, r, hx => by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [bitsOfNat_succ]
    simp only [List.cons_append, readBits]
    rw [readBits_bitsOfNat x b (H / 2) r (by omega)]
    simp only
    have h1 : H / 2 / 2 ^ x = H / 2 ^ (x + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have h2 : (if H.testBit 0 then 1 else 0) + 2 * (H / 2 % 2 ^ x) = H % 2 ^ (x + 1) := by
      rw [Nat.pow_succ', Nat.mod_mul]
      have : (if H.testBit 0 then 1 else 0) = H % 2 := by
        rw [Nat.testBit_zero]
        by_cases h : H % 2 = 1
        · simp [h]
        · have : H % 2 = 0 := by omega
          simp [this]
      rw [this]
    rw [h1, h2, show b + 1 - (x + 1) = b - x by omega]

variable (e : Env)

/-- The bits of the input bytes from offset `i` to the end of the input range. -/
def inBits (i : Nat) : List Bool :=
  bytesToBits ((e.IN.toList.drop i).take (e.i0 + e.sm0.avail_in.toNat - i))

/-- The bit sequence of a state: the bits of the buffer, then the bits of the unread input. -/
def Sg (H b i : Nat) : List Bool := bitsOfNat H b ++ inBits e i

theorem inBits_pull (i : Nat) (hi : i < e.i0 + e.sm0.avail_in.toNat) :
    inBits e i = byteBits (e.IN.getD i 0) ++ inBits e (i + 1) := by
  have hsz := e.hINsz
  unfold inBits
  have h1 : e.i0 + e.sm0.avail_in.toNat - i = (e.i0 + e.sm0.avail_in.toNat - (i + 1)) + 1 := by omega
  rw [h1]
  have hlt : i < e.IN.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
  simp only [bytesToBits, List.flatMap_cons]
  congr 1
  simp [Array.getD_eq_getD_getElem?, show i < e.IN.size by omega]

theorem Sg_pull (H b i : Nat) (hH : H < 2 ^ b) (hi : i < e.i0 + e.sm0.avail_in.toNat) :
    Sg e (H + (e.IN.getD i 0).toNat * 2 ^ b) (b + 8) (i + 1) = Sg e H b i := by
  unfold Sg
  rw [inBits_pull e i hi]
  have key : bitsOfNat (H + (e.IN.getD i 0).toNat * 2 ^ b) (b + 8) = bitsOfNat H b ++ byteBits (e.IN.getD i 0) := by
    unfold bitsOfNat byteBits
    rw [List.range_add, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro j hj
      have hj' : j < b := List.mem_range.mp hj
      rw [Nat.add_comm H, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hH]
      simp [hj']
    · rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_apply]
      rw [Nat.add_comm H, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hH]
      have hnl : ¬ (b + j < b) := by omega
      simp [hnl]
  rw [key, List.append_assoc]

end Zlib.Inffast.Proofs
