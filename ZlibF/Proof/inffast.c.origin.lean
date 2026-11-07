import ZlibF.Spec.InflateFastOrigin
import ZlibF.Proof.«inffast.c.final»

/-!
# Exact origin of the fast decoder's remaining input

The accounting and bit-list equations are retained together. In particular,
rollback recovers the actual unread input bytes, not an equal-length list.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.Origin
open ZlibF.Spec

/-- The entry registers already represent the complete initial suffix. -/
theorem initial_origin : Goal.initial_origin := by
  intro e
  exact ⟨by omega, by omega, e.hhold, by simp, by simp [initial]⟩

/-- Pulling the actual input byte preserves both origin equations. -/
theorem pull_preserves_origin : Goal.pull_preserves_origin := by
  intro e hold bits input used P available
  have byteBound : (e.IN.getD input 0).toNat + 1 ≤ 256 := by
    have := (e.IN.getD input 0).toNat_lt
    omega
  have normalized : hold + (e.IN.getD input 0).toNat * 2 ^ bits < 2 ^ (bits + 8) := by
    calc
      hold + (e.IN.getD input 0).toNat * 2 ^ bits <
          2 ^ bits + (e.IN.getD input 0).toNat * 2 ^ bits := Nat.add_lt_add_right P.normalized _
      _ = ((e.IN.getD input 0).toNat + 1) * 2 ^ bits := by rw [Nat.add_mul]; omega
      _ ≤ 256 * 2 ^ bits := Nat.mul_le_mul_right _ byteBound
      _ = 2 ^ (bits + 8) := by rw [Nat.pow_add, Nat.mul_comm]
  refine ⟨by have := P.inputLower; omega, by omega, normalized, ?_, ?_⟩
  · have := P.accounting
    have := P.inputLower
    omega
  · rw [Sg_pull e hold bits input P.normalized available]
    exact P.stream

/-- Dropping low bits consumes exactly that many original entry bits. -/
theorem drop_preserves_origin : Goal.drop_preserves_origin := by
  intro e hold bits input used count P available
  refine ⟨P.inputLower, P.inputUpper, ?_, ?_, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos count)).mpr
    rw [← Nat.pow_add, Nat.sub_add_cancel available]
    exact P.normalized
  · have := P.accounting
    omega
  · rw [Sg_drop hold bits input count available, P.stream, List.drop_drop]

private theorem in_bits_drop_bytes (e : Env) :
    ∀ (i k : Nat), i + k ≤ e.i0 + e.sm0.avail_in.toNat →
      (inBits e i).drop (8 * k) = inBits e (i + k) := by
  intro i k
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    intro available
    have first : i < e.i0 + e.sm0.avail_in.toNat := by omega
    rw [inBits_pull e i first, show 8 * (k + 1) = 8 + 8 * k by omega, ← List.drop_drop]
    have removed : (byteBits (e.IN.getD i 0) ++ inBits e (i + 1)).drop 8 = inBits e (i + 1) := by
      rw [List.drop_append]
      simp [byteBits]
    rw [removed, ih (i + 1) (by omega)]
    congr 1
    omega

private theorem low_bits_take (hold bits count : Nat) (available : count ≤ bits) :
    (bitsOfNat hold bits).take count = bitsOfNat hold count := by
  simp only [bitsOfNat, ← List.map_take, List.take_range, Nat.min_eq_left available]

private theorem low_bits_mask (hold count : Nat) :
    bitsOfNat (hold % 2 ^ count) count = bitsOfNat hold count := by
  unfold bitsOfNat
  apply List.map_congr_left
  intro j hj
  have bound : j < count := List.mem_range.mp hj
  simp [Nat.testBit_mod_two_pow, bound]

/-- Returning unused whole bytes preserves the exact remaining input.
Origin accounting identifies those bytes with the corresponding original
input range, and the mask retains the same low residual bits. -/
theorem rollback_preserves_origin : Goal.rollback_preserves_origin := by
  intro e hold bits input used P
  let returned := bits / 8
  let residual := bits % 8
  have decomposition : residual + 8 * returned = bits := Nat.mod_add_div bits 8
  have residualBound : residual < 8 := Nat.mod_lt _ (by decide)
  have rollbackBound : returned ≤ input - e.i0 := by
    have entryBits := e.hbits
    have accounting := P.accounting
    omega
  have newLower : e.i0 ≤ input - returned := by have := P.inputLower; omega
  have newUpper : input - returned ≤ e.i0 + e.sm0.avail_in.toNat := by
    have := P.inputUpper
    omega
  have residualAvailable : residual ≤ bits := by omega
  have accounting : used + residual = e.s0.bits.toNat + 8 * (input - returned - e.i0) := by
    have := P.accounting
    have := P.inputLower
    omega
  have originDrop : (initial e).drop (used + residual) = inBits e (input - returned) := by
    rw [accounting, initial, Sg, List.drop_append]
    have removed : (bitsOfNat e.s0.hold.toNat e.s0.bits.toNat).drop
        (e.s0.bits.toNat + 8 * (input - returned - e.i0)) = [] :=
      List.drop_eq_nil_of_le (by rw [bitsOfNat_length]; omega)
    rw [removed, List.nil_append, bitsOfNat_length, Nat.add_sub_cancel_left]
    have h := in_bits_drop_bytes e e.i0 (input - returned - e.i0) (by omega)
    simpa only [Nat.add_sub_of_le newLower] using h
  have tail : (Sg e hold bits input).drop residual = inBits e (input - returned) := by
    rw [P.stream, List.drop_drop]
    exact originDrop
  have head : (Sg e hold bits input).take residual = bitsOfNat hold residual := by
    rw [Sg, List.take_append_of_le_length (by rw [bitsOfNat_length]; exact residualAvailable)]
    exact low_bits_take hold bits residual residualAvailable
  have streamSame : Sg e (hold % 2 ^ residual) residual (input - returned) = Sg e hold bits input := by
    calc
      Sg e (hold % 2 ^ residual) residual (input - returned) =
          bitsOfNat hold residual ++ inBits e (input - returned) := by rw [Sg, low_bits_mask]
      _ = (Sg e hold bits input).take residual ++ (Sg e hold bits input).drop residual := by rw [head, tail]
      _ = Sg e hold bits input := List.take_append_drop _ _
  exact ⟨rollbackBound, streamSame, newLower, newUpper,
    Nat.mod_lt _ (Nat.two_pow_pos residual), accounting, streamSame.trans P.stream⟩

/-- The actual byte load, pointer advance and bounded word updates preserve
the same exact source suffix as the natural-number pull equation. -/
theorem actual_pull_preserves_origin : Goal.actual_pull_preserves_origin := by
  intro e bytes msg mode l i o used locals origin buffer available
  let next := pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))
  refine ⟨next, ?_, LS.pullL locals buffer available, ?_⟩
  · exact pull_run e (e.heap bytes msg mode) l i o locals buffer available
      (e.heap_bytes_in bytes msg mode)
  · have result := pull_preserves_origin e l.hold.toNat l.bits.toNat i used origin available
    simpa only [next, pullL_hold l _ _ locals.hb locals.hH, pullL_bits l _ _ locals.hb] using result

/-- The checked source shift and unsigned subtraction implement the
already justified low-bit drop without changing the heap. -/
theorem actual_drop_preserves_origin : Goal.actual_drop_preserves_origin := by
  intro e h l i o used count locals origin available
  have countBound : count.toNat < 64 := by have := locals.hb; omega
  refine ⟨?_, LS.dropL locals count available countBound, ?_⟩
  · simp only [C.run, shr64_eq (x := l.hold) (n := count.toUInt64)
        (by simpa only [UInt32.toNat_toUInt64] using countBound),
      bind_app, pure_app, dropL]
  · have result := drop_preserves_origin e l.hold.toNat l.bits.toNat i used count.toNat origin available
    simpa only [dropL_hold l count countBound, dropL_bits l count available] using result

/-- The actual pointer subtraction and checked mask computation recover
the same precise input suffix, including its returned whole bytes. -/
theorem actual_rollback_preserves_origin : Goal.actual_rollback_preserves_origin := by
  intro e bytes msg mode l i o used locals origin
  let returned := l.bits >>> 3
  let bits := l.bits - (returned <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  change C.run (do
      let input ← subn l.in_ returned
      let mask ← shl32 1 bits
      pure (input, l.hold &&& (mask - 1).toUInt64, bits)) (e.heap bytes msg mode) =
      .ok ((.ref (.blk e.ib) (i - l.bits.toNat / 8), hold, bits), e.heap bytes msg mode) ∧
    bits.toNat < 8 ∧ Inv e hold.toNat bits.toNat (i - l.bits.toNat / 8) used ∧
    Sg e hold.toNat bits.toNat (i - l.bits.toNat / 8) = Sg e l.hold.toNat l.bits.toNat i
  obtain ⟨rollbackBound, streamSame, rolledOrigin⟩ :=
    rollback_preserves_origin e l.hold.toNat l.bits.toNat i used origin
  have bitValue : bits.toNat = l.bits.toNat % 8 := bits_residual l.bits locals.hb
  have bitBound : bits.toNat < 8 := by rw [bitValue]; omega
  have maskValue : ((((1 : UInt32) <<< bits) - 1).toUInt64).toNat = 2 ^ bits.toNat - 1 := by
    rw [UInt32.toNat_toUInt64]
    exact u32_shl1_sub1 (by omega)
  have holdValue : hold.toNat = l.hold.toNat % 2 ^ (l.bits.toNat % 8) := by
    dsimp only [hold]
    rw [u64_and_mask maskValue, bitValue]
  have pointer : subn l.in_ returned (e.heap bytes msg mode) =
      .ok (.ref (.blk e.ib) (i - l.bits.toNat / 8), e.heap bytes msg mode) := by
    rw [locals.hin]
    have result := subn_ok (h := e.heap bytes msg mode) (r := BRef.blk e.ib) (a := e.IN)
      (e.heap_bytes_in bytes msg mode)
      (n := returned) (off := i)
      (by dsimp only [returned]; rw [bits_whole]; omega)
      (by have := locals.hi1; have := e.hINsz; omega)
    simpa only [returned, bits_whole, OkOn] using result
  refine ⟨?_, bitBound, ?_, ?_⟩
  · simp only [C.run, bind_app, pointer, pure_app,
      shl32_eq (x := 1) (n := bits) (by omega : bits.toNat < 32), hold]
  · simpa only [holdValue, bitValue] using rolledOrigin
  · simpa only [holdValue, bitValue] using streamSame

end Zlib.Inffast.Proofs
