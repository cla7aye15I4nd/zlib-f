import ZlibF.Proof.«public-inflate-small-queries»
import ZlibF.Spec.Functional.StreamQueries

namespace ZlibF.Spec.Public.InflatePrimeProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public.InflateQueryProof

def primeBits (bits value : Int32) : UInt64 :=
  Zlib.Inflate.i2ul ((value.toInt64 &&& (((1 : Int64) <<< bits.toInt64) - 1)).toInt32)

/-- The state after `inflatePrime` inserted `bits` bits (`1 ≤ bits ≤ 16`, they fit): `hold += value << bits_in_hold`. -/
def primeState (bits value : Int32) (st : InflateState) : InflateState :=
  { st with hold := st.hold + (primeBits bits value <<< st.bits.toUInt64), bits := st.bits + Zlib.Inflate.i2u bits }

theorem i2u_toNat {b : Int32} (h0 : 0 ≤ b.toInt) : (i2u b).toNat = b.toInt.toNat := by
  unfold i2u
  rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le]; simpa using h0)]
  rfl

theorem int32_pos {b : Int32} (h : 0 < b) : 0 < b.toInt := by
  have := Int32.lt_iff_toInt_lt.mp h; simpa using this

theorem int32_neg_lt {b : Int32} (h : b < 0) : b.toInt < 0 := by
  have := Int32.lt_iff_toInt_lt.mp h; simpa using this

theorem int32_gt16 {b : Int32} : 16 < b ↔ 16 < b.toInt := by
  rw [Int32.lt_iff_toInt_lt]
  change (16 : Int) < b.toInt ↔ 16 < b.toInt
  rfl

theorem inflatePrime_record {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hl : Live h r zs z st) (hb39 : st.bits.toNat ≤ 39) (bits value : Int32) :
    (bits = 0 → C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, h)) ∧
    (bits < 0 → C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, setI h zs { st with hold := 0, bits := 0 })) ∧
    (0 < bits → (16 < bits.toInt ∨ 32 < st.bits.toNat + bits.toInt.toNat) →
      C.run (inflatePrime (some r) bits value) h = .ok (Z_STREAM_ERROR, h)) ∧
    (0 < bits → bits.toInt ≤ 16 → st.bits.toNat + bits.toInt.toNat ≤ 32 →
      C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, setI h zs (primeState bits value st))) := by
  refine ⟨fun h0 => ?_, fun hn => ?_, fun hp hbad => ?_, fun hp h16 hfit => ?_⟩
  · subst h0
    show inflatePrime (some r) 0 value h = _
    unfold inflatePrime; isimp [stateCheck_live hl]
  · have h0 : bits ≠ 0 := by intro e; subst e; have := int32_neg_lt hn; simp at this
    show inflatePrime (some r) bits value h = _
    unfold inflatePrime; isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, h0, hn]
  · have hpi := int32_pos hp
    have h0 : bits ≠ 0 := by intro e; subst e; simp at hpi
    have hn : ¬ bits < 0 := fun hn => by have := int32_neg_lt hn; omega
    show inflatePrime (some r) bits value h = _
    unfold inflatePrime
    by_cases h16 : 16 < bits
    · isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, h0, hn, h16]
    · have h16'' : ¬ 16 < bits.toInt := fun hh => h16 (int32_gt16.mpr hh)
      have hgt : 32 < st.bits + i2u bits := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, i2u_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
        have : (32 : UInt32).toNat = 32 := rfl
        omega
      isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, h0, hn, h16, hgt]
  · have hpi := int32_pos hp
    have h0 : bits ≠ 0 := by intro e; subst e; simp at hpi
    have hn : ¬ bits < 0 := fun hn => by have := int32_neg_lt hn; omega
    have h16 : ¬ 16 < bits := fun hh => by have := int32_gt16.mp hh; omega
    have hu := i2u_toNat (b := bits) (by omega)
    have hgt : ¬ 32 < st.bits + i2u bits := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, hu, Nat.mod_eq_of_lt (by omega)]
      have : (32 : UInt32).toNat = 32 := rfl
      omega
    have hlt : st.bits < 64 := by rw [UInt32.lt_iff_toNat_lt]; have : (64 : UInt32).toNat = 64 := rfl; omega
    show inflatePrime (some r) bits value h = _
    unfold inflatePrime
    isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, h0, hn, h16, hgt, shl64, hlt, primeState, primeBits]

/-- The source long-width mask agrees with the public unsigned mask for every
accepted positive count. -/
theorem primeBits_public (bits value : Int32) (h0 : 0 < bits.toInt) (h16 : bits.toInt ≤ 16) :
    primeBits bits value = (value.toUInt32 &&& ((1 <<< bits.toUInt32) - 1)).toUInt64 := by
  have hc : bits.toInt = 1 ∨ bits.toInt = 2 ∨ bits.toInt = 3 ∨ bits.toInt = 4 ∨ bits.toInt = 5 ∨ bits.toInt = 6 ∨ bits.toInt = 7 ∨ bits.toInt = 8 ∨ bits.toInt = 9 ∨ bits.toInt = 10 ∨ bits.toInt = 11 ∨ bits.toInt = 12 ∨ bits.toInt = 13 ∨ bits.toInt = 14 ∨ bits.toInt = 15 ∨ bits.toInt = 16 := by omega
  have hb : bits = Int32.ofInt bits.toInt := (Int32.ofInt_toInt bits).symm
  rcases hc with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  all_goals
    rw [hcase] at hb
    subst bits
    unfold primeBits i2ul
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 32
    · simp [BitVec.getLsbD_signExtend, hi]
    · have hpow : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      simp [BitVec.getLsbD_signExtend, BitVec.getLsbD_ofNat, hi,
        Nat.testBit_lt_two_pow (show 1 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 3 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 7 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 15 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 31 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 63 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 127 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 255 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 511 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 1023 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 2047 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 4095 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 8191 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 16383 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 32767 < 2 ^ i by omega),
        Nat.testBit_lt_two_pow (show 65535 < 2 ^ i by omega)]

/-- `inflatePrime` rejects a state-check input that is not initialised. -/
theorem inflatePrime_reject {h : Heap} {p : ZStreamPtr}
    (hd : StreamDom h p) (hn : ¬ Initialised h p) (bits value : Int32) :
    C.run (inflatePrime p bits value) h = .ok (Z_STREAM_ERROR, h) := by
  show inflatePrime p bits value h = _
  unfold inflatePrime
  simp [bind_app, notInit_check hd hn, pure_app, Z_STREAM_ERROR]


/-- `int inflatePrime(z_streamp strm, int bits, int value)`
The exact public result, state, frame and ownership contract. -/
theorem prime_public : Goal.inflatePrime := by
  intro bits value
  constructor
  · intro h p hr
    exact inflatePrime_reject (refused_dom hr) (refused_not_initialised hr) bits value
  · intro h r i z s hv hbits
    rcases hv with ⟨hz, hstate, hi, hb, ha, hf, hlo, hhi⟩
    have hl : Live h r i z s := ⟨hz, hi, hstate, hb, ⟨hlo, hhi⟩, ha, hf⟩
    have run := inflatePrime_record hl hbits bits value
    by_cases hzero : bits = 0
    · simpa [hzero] using run.1 hzero
    · by_cases hneg : bits.toInt < 0
      · have hn : bits < 0 := Int32.lt_iff_toInt_lt.mpr (by simpa using hneg)
        simpa [hzero, hneg, putInflate, setI] using run.2.1 hn
      · have hpos : 0 < bits := by
          apply Int32.lt_iff_toInt_lt.mpr
          have hne : bits.toInt ≠ 0 := fun h => hzero (Int32.toInt_inj.mp (by simpa using h))
          simp only [Int32.toInt_zero]
          omega
        by_cases hbad : 16 < bits.toInt ∨ 32 < s.bits.toNat + bits.toInt.toNat
        · rw [ite_eq_right hzero, ite_eq_right hneg, ite_eq_left hbad]
          exact run.2.2.1 hpos hbad
        · have hp := int32_pos hpos
          have hh16 : bits.toInt ≤ 16 := by omega
          have hfit : s.bits.toNat + bits.toInt.toNat ≤ 32 := by omega
          have hpbit := primeBits_public bits value hp hh16
          rw [ite_eq_right hzero, ite_eq_right hneg, ite_eq_right hbad]
          simpa [primeState, hpbit, i2u, putInflate, setI] using run.2.2.2 hpos hh16 hfit


#print axioms prime_public
end ZlibF.Spec.Public.InflatePrimeProof
