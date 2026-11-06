import ZlibF.Proof.«public-inflate-small-queries»

namespace ZlibF.Spec.Public.InflateMarkProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public.InflateQueryProof

def markValue (st : InflateState) : Int :=
  st.back.toInt * 65536 + (if st.mode = COPY then st.length.toNat else if st.mode = MATCH then (st.was - st.length).toNat else 0)


theorem mark_hi (b : Int32) :
    ((b.toInt64.toUInt64 <<< (16 : UInt64)).toInt64).toInt = b.toInt * 65536 := by
  have hb1 := b.le_toInt
  have hb2 := b.toInt_lt
  have : (b.toInt64.toUInt64 <<< (16 : UInt64)).toInt64 = b.toInt64 * 65536 := by
    apply Int64.toBitVec_inj.mp
    rw [UInt64.toBitVec_toInt64, UInt64.toBitVec_shiftLeft, Int64.toBitVec_mul, BitVec.shiftLeft_eq',
      BitVec.shiftLeft_eq_mul_twoPow]
    have e1 : ((16 : UInt64).toBitVec % 64).toNat = 16 := rfl
    rw [e1]
    have e2 : BitVec.twoPow 64 16 = (65536 : Int64).toBitVec := by decide
    rw [e2]
    rfl
  rw [this, Int64.toInt_mul]
  simp only [Int32.toInt_toInt64]
  rw [Int.bmod_eq_iff (by decide)]
  have e3 : (65536 : Int64).toInt = 65536 := by decide
  have e4 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  rw [e3, e4]
  refine ⟨by omega, by omega, by simp⟩

theorem inflateMark_spec {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) :
    ∃ v, C.run (inflateMark (some r)) h = .ok (v, h) ∧ v.toInt = markValue st := by
  have hb1 := st.back.le_toInt
  have hb2 := st.back.toInt_lt
  have hl := st.length.toNat_lt
  have hw := (st.was - st.length).toNat_lt
  have key : ∀ lo : UInt32, ∃ v, (do
      let hi : Int64 := ((st.back.toInt64.toUInt64) <<< 16).toInt64
      chkI64 (hi.toInt + lo.toNat) : M Int64) h = .ok (v, h) ∧ v.toInt = st.back.toInt * 65536 + lo.toNat := by
    intro lo
    have hlo := lo.toNat_lt
    have hm := mark_hi st.back
    have hr : -9223372036854775808 ≤ st.back.toInt * 65536 + (lo.toNat : Int) ∧
        st.back.toInt * 65536 + (lo.toNat : Int) < 9223372036854775808 := by omega
    refine ⟨Int64.ofInt (st.back.toInt * 65536 + lo.toNat), ?_, ?_⟩
    · simp only [bind_app, pure_app]
      have : (((st.back.toInt64.toUInt64) <<< 16).toInt64).toInt = st.back.toInt * 65536 := mark_hi st.back
      simp [chkI64, this, hr.1, hr.2]
    · rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have hrun : inflateMark (some r) h = (do
      let hi : Int64 := ((st.back.toInt64.toUInt64) <<< 16).toInt64
      let lo : UInt32 := if st.mode = COPY then st.length else if st.mode = MATCH then st.was - st.length else 0
      chkI64 (hi.toInt + lo.toNat) : M Int64) h := by
    unfold inflateMark
    isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs]
  rw [C.run, hrun]
  obtain ⟨v, hv, hv2⟩ := key (if st.mode = COPY then st.length else if st.mode = MATCH then st.was - st.length else 0)
  refine ⟨v, ?_, ?_⟩
  · simpa using hv
  · rw [hv2]; unfold markValue
    by_cases c1 : st.mode = COPY
    · simp [c1]
    · have hne : (MATCH : UInt32) ≠ COPY := by decide
      by_cases c2 : st.mode = MATCH
      · simp [c1, c2, hne]
      · simp [c1, c2]


/-- `long inflateMark(z_streamp strm)` returns the exact copy or match position. -/
theorem mark_public : Goal.inflateMark := by
  constructor
  · intro h p hr
    show inflateMark p h = _
    unfold inflateMark
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app]
    decide
  · intro h r i z s hv
    rcases hv with ⟨hz, hstate, hi, hb, ha, hf, hlo, hhi⟩
    have hl : Live h r i z s := ⟨hz, hi, hstate, hb, ⟨hlo, hhi⟩, ha, hf⟩
    obtain ⟨v, hv, he⟩ := inflateMark_spec hl
    simp only [markValue] at he
    rw [← he, Int64.ofInt_toInt]
    exact hv

#print axioms mark_public
end ZlibF.Spec.Public.InflateMarkProof
