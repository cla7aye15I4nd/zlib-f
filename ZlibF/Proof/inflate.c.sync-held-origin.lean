import ZlibF.Proof.«inflate.c.copy-both-origin»
import ZlibF.Proof.«inflate.c.sync4»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Repeated real byte shifts divide the held integer by the corresponding
power of two, without introducing a modulo shift-count assumption. -/
theorem shr8N_toNat (count : Nat) (word : UInt64) :
    (shr8N count word).toNat = word.toNat / 2 ^ (8 * count) := by
  induction count with
  | zero => simp [shr8N]
  | succ count ih =>
    change (shr8N count word >>> (8 : UInt32).toUInt64).toNat = _
    rw [Zlib.Inffast.Proofs.u64_shr (n := 8) (by decide), ih,
      Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2

/-- The actual sync restore drains the held word completely when its
incoming bit bound was established by initialized history. Good's width
bound alone would not suffice to justify the empty bit buffer. -/
theorem syncFirstState_hold_zero {s : InflateState}
    (held : s.hold.toNat < 2 ^ s.bits.toNat) : (syncFirstState s).hold = 0 := by
  apply UInt64.toNat_inj.mp
  change (shr8N (syncNB s) (syncHold0 s)).toNat = 0
  rw [shr8N_toNat]
  have partialShift : (syncHold0 s).toNat = s.hold.toNat / 2 ^ (s.bits.toNat % 8) := by
    unfold syncHold0
    rw [Zlib.Inffast.Proofs.u64_shr (by rw [sync_and7_toNat]; omega), sync_and7_toNat]
  rw [partialShift, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have count : s.bits.toNat % 8 + 8 * syncNB s = s.bits.toNat := by
    unfold syncNB
    omega
  rw [count]
  exact Nat.div_eq_of_lt held

#print axioms shr8N_toNat
#print axioms syncFirstState_hold_zero
end Zlib.Inflate.Proofs
