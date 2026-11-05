import ZlibF.Proof.«inflate.c.misc»

/-!
# inflate.c: `inflatePrime`, `inflateGetHeader`, `inflateInit_`
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem i2u_toNat {b : Int32} (h0 : 0 ≤ b.toInt) : (i2u b).toNat = b.toInt.toNat := by
  unfold i2u
  rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le]; simpa using h0)]
  rfl

theorem int32_pos {b : Int32} (h : 0 < b) : 0 < b.toInt := by
  have := Int32.lt_iff_toInt_lt.mp h; simpa using this

theorem int32_neg_lt {b : Int32} (h : b < 0) : b.toInt < 0 := by
  have := Int32.lt_iff_toInt_lt.mp h; simpa using this

theorem int32_gt16 {b : Int32} : 16 < b ↔ 16 < b.toInt := by
  rw [show (16 : Int32) = Int32.ofInt 16 from rfl, Int32.lt_iff_toInt_lt, int32_ofInt_toInt 16 (by omega) (by omega)]

/-- **inflatePrime, specification and safety.** On an initialised stream the call never faults and the invariants hold
afterwards. `bits = 0`: `Z_OK`, nothing changes. `bits < 0`: `Z_OK`, the bit buffer is emptied. `bits > 16`, or more than
32 bits in the buffer afterwards: `Z_STREAM_ERROR`, nothing changes. Otherwise `Z_OK` and the low `bits` bits of `value`
are put above the bits already held (`primeState`). -/
theorem inflatePrime_spec {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (bits value : Int32) :
    (bits = 0 → C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, h)) ∧
    (bits < 0 → C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, setI h zs { st with hold := 0, bits := 0 }) ∧
      Good (setI h zs { st with hold := 0, bits := 0 }) r zs z { st with hold := 0, bits := 0 }) ∧
    (0 < bits → (16 < bits.toInt ∨ 32 < st.bits.toNat + bits.toInt.toNat) →
      C.run (inflatePrime (some r) bits value) h = .ok (Z_STREAM_ERROR, h)) ∧
    (0 < bits → bits.toInt ≤ 16 → st.bits.toNat + bits.toInt.toNat ≤ 32 →
      C.run (inflatePrime (some r) bits value) h = .ok (Z_OK, setI h zs (primeState bits value st)) ∧
      Good (setI h zs (primeState bits value st)) r zs z (primeState bits value st)) := by
  have hL := hG.live
  have hb39 := hG.inv.bits
  refine ⟨fun h0 => ?_, fun hn => ?_, fun hp hbad => ?_, fun hp h16 hfit => ?_⟩
  · subst h0
    show inflatePrime (some r) 0 value h = _
    unfold inflatePrime; isimp [stateCheck_live hL]
  · have h0 : bits ≠ 0 := by intro e; subst e; have := int32_neg_lt hn; simp at this
    refine ⟨?_, good_state hG rfl hL.mode (hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp) rfl rfl rfl)⟩
    show inflatePrime (some r) bits value h = _
    unfold inflatePrime; isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, h0, hn]
  · have hpi := int32_pos hp
    have h0 : bits ≠ 0 := by intro e; subst e; simp at hpi
    have hn : ¬ bits < 0 := fun hn => by have := int32_neg_lt hn; omega
    show inflatePrime (some r) bits value h = _
    unfold inflatePrime
    by_cases h16 : 16 < bits
    · isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, h0, hn, h16]
    · have h16'' : ¬ 16 < bits.toInt := fun hh => h16 (int32_gt16.mpr hh)
      have h16' : bits.toInt ≤ 16 := by omega
      have hgt : 32 < st.bits + i2u bits := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, i2u_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
        have : (32 : UInt32).toNat = 32 := rfl
        omega
      isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, h0, hn, h16, hgt]
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
    have hrun : inflatePrime (some r) bits value h = .ok (Z_OK, setI h zs (primeState bits value st)) := by
      unfold inflatePrime
      isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, h0, hn, h16, hgt, shl64, hlt, primeState, primeBits]
    refine ⟨hrun, good_state hG rfl hL.mode ?_⟩
    have hsum : (st.bits + i2u bits).toNat = st.bits.toNat + bits.toInt.toNat := by
      rw [UInt32.toNat_add, hu, Nat.mod_eq_of_lt (by omega)]
    exact hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl (by show (st.bits + i2u bits).toNat ≤ 39; omega) rfl rfl rfl

end Zlib.Inflate.Proofs
