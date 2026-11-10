import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«public-inflate-prime»
import ZlibF.Math.«bit-buffer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual signed long-width mask has fewer than the requested bits,
for every accepted positive count and every signed value. -/
theorem primeBits_bound (bits value : Int32) (positive : 0 < bits.toInt) (small : bits.toInt ≤ 16) :
    (primeBits bits value).toNat < 2 ^ bits.toInt.toNat := by
  have mask := ZlibF.Spec.Public.InflatePrimeProof.primeBits_public bits value positive small
  change primeBits bits value = _ at mask
  have count : bits.toUInt32.toNat = bits.toInt.toNat := i2u_toNat (by omega)
  have countBound : bits.toUInt32.toNat < 32 := by rw [count]; omega
  rw [mask, UInt32.toNat_toUInt64, UInt32.toNat_and, mask_toNat _ countBound, count]
  have le : value.toUInt32.toNat &&& (2 ^ bits.toInt.toNat - 1) ≤ 2 ^ bits.toInt.toNat - 1 := Nat.and_le_right
  have power := Nat.two_pow_pos bits.toInt.toNat
  omega

/-- Appending the actual masked bits preserves normalized held bits.
The admitted total is at most 32, so neither shift nor addition wraps. -/
theorem primeState_held {s : InflateState} (held : s.hold.toNat < 2 ^ s.bits.toNat)
    (bits value : Int32) (positive : 0 < bits.toInt) (small : bits.toInt ≤ 16)
    (fit : s.bits.toNat + bits.toInt.toNat ≤ 32) :
    (primeState bits value s).hold.toNat < 2 ^ (primeState bits value s).bits.toNat := by
  have mask := primeBits_bound bits value positive small
  have count : (i2u bits).toNat = bits.toInt.toNat := i2u_toNat (by omega)
  have countEq : (s.bits + i2u bits).toNat = s.bits.toNat + bits.toInt.toNat := by
    rw [UInt32.toNat_add, count, Nat.mod_eq_of_lt (by omega)]
  change (s.hold + (primeBits bits value <<< s.bits.toUInt64)).toNat < 2 ^ (s.bits + i2u bits).toNat
  rw [countEq]
  exact ZlibF.Math.BitBuffer.append_normalized s.hold (primeBits bits value) s.bits bits.toInt.toNat
    held mask (by omega) (by omega)

/-- A real private bit-buffer update retains every other default invariant
clause. Its held-bit bound is proved separately from the source arithmetic. -/
theorem DefaultStateJ.set_bits {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold := hold, bits := bits }) r zs z { s with hold := hold, bits := bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    DefaultStateJ (setI h zs { s with hold := hold, bits := bits }) r zs z { s with hold := hold, bits := bits } := by
  obtain ⟨tables, lengths⟩ := table_clauses_set_bits invariant.good.live.hs hold bits invariant.tables invariant.lengths
  exact ⟨⟨good, tables, ⟨invariant.pending.sane, invariant.pending.lenext,
    invariant.pending.dist, invariant.pending.distext, invariant.pending.matching⟩, lengths, invariant.headerLengths, held,
    invariant.window, invariant.wrapper, invariant.header, invariant.modes, invariant.trailer,
    invariant.globals, invariant.platform.with_istates _⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- `int inflatePrime(z_streamp strm, int bits, int value)`.
All signed arguments preserve the complete default relation and allocator.
Clearing, no-op, refusal and accepted insertion call the actual translated
operation; no table or held-bit callee contract is assumed. -/
theorem inflatePrime_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (bits value : Int32) :
    ∃ rc after state, C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ DefAlloc z ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR) := by
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec invariant.good bits value
  by_cases equal : bits = 0
  · exact ⟨Z_OK, h, s, zero equal, invariant, allocator, Or.inl rfl⟩
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    have current := invariant.set_bits 0 0 good (by change 0 < 1; decide)
    exact ⟨Z_OK, _, _, run, current, allocator, Or.inl rfl⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    change ¬ bits.toInt < 0 at negative
    change 0 < bits.toInt
    have notZero : bits.toInt ≠ 0 := by
      intro eq
      apply equal
      exact Int32.toInt_inj.mp eq
    omega
  by_cases wide : 16 < bits.toInt
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inl wide), invariant, allocator, Or.inr rfl⟩
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inr full), invariant, allocator, Or.inr rfl⟩
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  have current := invariant.set_bits (primeState bits value s).hold (primeState bits value s).bits good
    (primeState_held invariant.held bits value (int32_pos positive) (by omega) (by omega))
  exact ⟨Z_OK, _, _, run, current, allocator, Or.inl rfl⟩

end Zlib.Inflate.Proofs
