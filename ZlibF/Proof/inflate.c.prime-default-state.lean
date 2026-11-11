import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.table-prime»
import ZlibF.Proof.«public-inflate-prime»
import ZlibF.Proof.«inffast.c.base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Prime changes only the private bit buffer. A checked new held value
therefore transports every other default-history clause. -/
theorem DefaultStateJ.prime_set_bits
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold, bits }) r zs z { s with hold, bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    DefaultStateJ (setI h zs { s with hold, bits }) r zs z { s with hold, bits } := by
  obtain ⟨tables, lengths⟩ := table_clauses_set_bits invariant.good.live.hs
    hold bits invariant.tables invariant.lengths
  refine ⟨⟨good, tables, ?_, lengths, ?_, held, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · refine ⟨invariant.pending.sane, ?_, ?_, ?_, ?_⟩
    · simpa [LengthExtraSafe, BackBound] using invariant.pending.lenext
    · simpa [DistanceSafe, PendingLengthSafe, BackBound] using invariant.pending.dist
    · simpa [DistanceExtraSafe, PendingLengthSafe, BackBound] using invariant.pending.distext
    · simpa [MatchSafe] using invariant.pending.matching
  · simpa [LengthHeaderInvariant] using invariant.headerLengths
  · exact invariant.window
  · exact invariant.wrapper
  · exact HeaderMemory.step invariant.header invariant.good good rfl rfl (byte_view_sizes_setI h zs _)
  · exact invariant.modes
  · exact invariant.trailer
  · simpa only [LibraryGlobals, setI] using invariant.globals
  · exact invariant.platform.with_istates _
  · exact invariant.requestedBits
  · exact invariant.requestedWrap
  · exact invariant.phase

/-- The accepted positive prime count inserts only low-order source bits.
The 32-bit acceptance check keeps the entire held word below 2^32. -/
theorem primeState_held
    (s : InflateState) (bits value : Int32)
    (old : s.hold.toNat < 2 ^ s.bits.toNat)
    (positive : 0 < bits) (width : bits.toInt ≤ 16)
    (fit : s.bits.toNat + bits.toInt.toNat ≤ 32) :
    (primeState bits value s).hold.toNat <
      2 ^ (primeState bits value s).bits.toNat := by
  have positiveNat : 0 < bits.toInt := int32_pos positive
  have count : (i2u bits).toNat = bits.toInt.toNat :=
    i2u_toNat (by omega)
  have mask : (((1 : UInt32) <<< bits.toUInt32) - 1).toNat =
      2 ^ bits.toInt.toNat - 1 := by
    have small : bits.toUInt32.toNat < 32 := by
      rw [show bits.toUInt32 = i2u bits from rfl, count]
      omega
    simpa only [show bits.toUInt32 = i2u bits from rfl, count] using
      Zlib.Inffast.Proofs.u32_shl1_sub1 small
  have primePublic := ZlibF.Spec.Public.InflatePrimeProof.primeBits_public
    bits value positiveNat width
  have primeBound : (primeBits bits value).toNat < 2 ^ bits.toInt.toNat := by
    have same : primeBits bits value =
        ZlibF.Spec.Public.InflatePrimeProof.primeBits bits value := rfl
    rw [same, primePublic, UInt32.toNat_toUInt64]
    rw [Zlib.Inffast.Proofs.u32_and_mask mask]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have sumBound : s.hold.toNat + (primeBits bits value).toNat *
      2 ^ s.bits.toNat < 2 ^ (s.bits.toNat + bits.toInt.toNat) := by
    have upper := Nat.mul_le_mul_right (2 ^ s.bits.toNat)
      (show (primeBits bits value).toNat + 1 ≤ 2 ^ bits.toInt.toNat by omega)
    rw [Nat.add_mul, Nat.one_mul] at upper
    have powEq : 2 ^ bits.toInt.toNat * 2 ^ s.bits.toNat =
        2 ^ (s.bits.toNat + bits.toInt.toNat) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    omega
  have sizeBound : 2 ^ (s.bits.toNat + bits.toInt.toNat) ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by decide) fit
  have shiftBound : (primeBits bits value).toNat * 2 ^ s.bits.toNat < 2 ^ 64 := by
    omega
  have shift : (primeBits bits value <<< s.bits.toUInt64).toNat =
      (primeBits bits value).toNat * 2 ^ s.bits.toNat := by
    have oldSmall : s.bits.toNat < 64 := by omega
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      Nat.mod_eq_of_lt oldSmall, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt shiftBound
  have nextBits : (s.bits + i2u bits).toNat =
      s.bits.toNat + bits.toInt.toNat := by
    rw [UInt32.toNat_add, count]
    exact Nat.mod_eq_of_lt (by omega)
  have nextHold : (s.hold + (primeBits bits value <<< s.bits.toUInt64)).toNat =
      s.hold.toNat + (primeBits bits value).toNat * 2 ^ s.bits.toNat := by
    rw [UInt64.toNat_add, shift]
    exact Nat.mod_eq_of_lt (by omega)
  simpa only [primeState, nextHold, nextBits] using sumBound

/-- Every signed prime request preserves the initialized default state.
Rejected requests leave the heap unchanged; accepted requests retain the
checked bit-buffer bound. This is an internal history transition. -/
theorem inflatePrime_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (bits value : Int32) :
    ∃ rc after state,
      C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧
      (rc = Z_OK ∨ rc = Z_STREAM_ERROR) := by
  obtain ⟨zero, clear, reject, insert⟩ :=
    inflatePrime_spec invariant.good bits value
  by_cases equal : bits = 0
  · exact ⟨Z_OK, h, s, zero equal, invariant, Or.inl rfl⟩
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    have held : (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat := by decide
    exact ⟨Z_OK, _, _, run,
      invariant.prime_set_bits 0 0 good held, Or.inl rfl⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have notZero : bits.toInt ≠ 0 := by
      intro eq
      apply equal
      exact Int32.toInt_inj.mp eq
    omega
  by_cases wide : 16 < bits.toInt
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inl wide),
      invariant, Or.inr rfl⟩
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inr full),
      invariant, Or.inr rfl⟩
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  have held := primeState_held s bits value invariant.held positive
    (by omega) (by omega)
  exact ⟨Z_OK, _, _, run,
    invariant.prime_set_bits _ _ good held, Or.inl rfl⟩

#print axioms DefaultStateJ.prime_set_bits
#print axioms primeState_held
#print axioms inflatePrime_default_state
end Zlib.Inflate.Proofs
