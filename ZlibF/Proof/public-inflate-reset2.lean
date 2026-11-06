import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.init»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec

namespace ZlibF.Spec.Public.InflateReset2Proof

theorem params_equiv (w : Int32) :
    reset2Params w = (Api.inflWbits w.toInt).map (fun (wr, n) =>
      ((match wr with | .raw => 0 | .zlib => 5 | .gzip => 6 | .auto => 7 : Int32), Int32.ofInt n)) := by
  by_cases hlo : w.toInt < -15
  · have hn : w < 0 := Int32.lt_iff_toInt_lt.mpr (by simpa using (show w.toInt < 0 by omega))
    have h15 : w < -15 := Int32.lt_iff_toInt_lt.mpr (by simpa using hlo)
    simp [reset2Params, hn, h15, Api.inflWbits, hlo, show w.toInt < 0 by omega]
  · by_cases hhi : 48 ≤ w.toInt
    · have hn : ¬ w < 0 := fun x => by have := Int32.lt_iff_toInt_lt.mp x; simp at this; omega
      have h48 : ¬ w < 48 := fun x => by have := Int32.lt_iff_toInt_lt.mp x; simp at this; omega
      have h16 : 15 < w := Int32.lt_iff_toInt_lt.mpr (by simpa using (show 15 < w.toInt by omega))
      have hb : badBits w = true := by simp [badBits, h16, show w ≠ 0 by intro h; subst w; simp at hhi]
      have hdiv0 : w.toInt / 16 ≠ 0 := by omega
      have hdiv1 : w.toInt / 16 ≠ 1 := by omega
      have hdiv2 : w.toInt / 16 ≠ 2 := by omega
      simp [reset2Params, hn, h48, hb, Api.inflWbits, show ¬ w.toInt < 0 by omega, hdiv0, hdiv1, hdiv2]
    · have hc : w.toInt = -15 ∨ w.toInt = -14 ∨ w.toInt = -13 ∨ w.toInt = -12 ∨
        w.toInt = -11 ∨ w.toInt = -10 ∨ w.toInt = -9 ∨ w.toInt = -8 ∨
        w.toInt = -7 ∨ w.toInt = -6 ∨ w.toInt = -5 ∨ w.toInt = -4 ∨
        w.toInt = -3 ∨ w.toInt = -2 ∨ w.toInt = -1 ∨ w.toInt = 0 ∨
        w.toInt = 1 ∨ w.toInt = 2 ∨ w.toInt = 3 ∨ w.toInt = 4 ∨
        w.toInt = 5 ∨ w.toInt = 6 ∨ w.toInt = 7 ∨ w.toInt = 8 ∨
        w.toInt = 9 ∨ w.toInt = 10 ∨ w.toInt = 11 ∨ w.toInt = 12 ∨
        w.toInt = 13 ∨ w.toInt = 14 ∨ w.toInt = 15 ∨ w.toInt = 16 ∨
        w.toInt = 17 ∨ w.toInt = 18 ∨ w.toInt = 19 ∨ w.toInt = 20 ∨
        w.toInt = 21 ∨ w.toInt = 22 ∨ w.toInt = 23 ∨ w.toInt = 24 ∨
        w.toInt = 25 ∨ w.toInt = 26 ∨ w.toInt = 27 ∨ w.toInt = 28 ∨
        w.toInt = 29 ∨ w.toInt = 30 ∨ w.toInt = 31 ∨ w.toInt = 32 ∨
        w.toInt = 33 ∨ w.toInt = 34 ∨ w.toInt = 35 ∨ w.toInt = 36 ∨
        w.toInt = 37 ∨ w.toInt = 38 ∨ w.toInt = 39 ∨ w.toInt = 40 ∨
        w.toInt = 41 ∨ w.toInt = 42 ∨ w.toInt = 43 ∨ w.toInt = 44 ∨
        w.toInt = 45 ∨ w.toInt = 46 ∨ w.toInt = 47 := by omega
      have hw : w = Int32.ofInt w.toInt := (Int32.ofInt_toInt w).symm
      rcases hc with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase
      all_goals rw [hcase] at hw; subst w; decide

#print axioms params_equiv

theorem api_bits_bound (w : Int) (wr : Api.Wrap) (n : Nat)
    (h : Api.inflWbits w = some (wr, n)) : n ≤ 15 := by
  unfold Api.inflWbits at h
  repeat' split at h
  all_goals simp_all <;> omega

/-- `int inflateReset2(z_streamp strm, int windowBits)`
The exact public result, state, frame and ownership contract. -/
theorem reset2_public : Goal.inflateReset2 := by
  intro h r i z s wb hv hf hwin
  rcases hv with ⟨hz,hstate,hi,hback,ha,hfree,hlo,hhi⟩
  have hl : Live h r i z s := ⟨hz,hi,hstate,hback,⟨hlo,hhi⟩,ha,hfree⟩
  have hw : WindowOk h s.window := hwin
  have hr := inflateReset2_run hl hf hw wb
  have hp := params_equiv wb
  cases hap : Api.inflWbits wb.toInt with
  | none =>
    rw [hap] at hp
    simp only [Option.map_none] at hp
    rw [hp] at hr
    simpa [hap, C.run] using hr
  | some pair =>
    obtain ⟨wr,n⟩ := pair
    have hn : n ≤ 15 := api_bits_bound wb.toInt wr n hap
    have hcast : (Int32.ofInt n).toUInt32 = UInt32.ofNat n := by rfl
    have hnat : (UInt32.ofNat n).toNat = n := by change n % 2 ^ 32 = n; exact Nat.mod_eq_of_lt (by omega)
    have hn32 : n < 4294967296 := by omega
    have hbiteq : (s.wbits = (Int32.ofInt n).toUInt32) ↔ s.wbits.toNat = n := by
      rw [hcast, ← UInt32.toNat_inj, hnat]
    rw [hap] at hp
    simp only [Option.map_some] at hp
    rw [hp] at hr
    cases wr <;>
      simp only at hr ⊢
    all_goals
      have hrun := hr.2
      by_cases hb : s.wbits.toNat = n
      · have he : s.wbits = (Int32.ofInt n).toUInt32 := hbiteq.mpr hb
        simpa [hap, C.run, hb, he, reset2Heap, reset2Pre, resetPre, resetKeepState, resetKeepStream,
          inflateResetState, inflateResetStream, setI, putInflate, i2u, i2ul, hcast, hn32, hnat] using hrun
      · have he : s.wbits ≠ (Int32.ofInt n).toUInt32 := fun x => hb (hbiteq.mp x)
        have he' : s.wbits ≠ UInt32.ofNat n := by simpa [hcast] using he
        rcases hwin with hnull | ⟨b, a, hptr, _, _⟩
        · simpa [hap, C.run, hb, he, hnull, reset2Heap, reset2Pre, resetPre, resetKeepState, resetKeepStream,
            inflateResetState, inflateResetStream, setI, putInflate, i2u, i2ul, hcast, hn32, hnat, he', dropWindow, freeWin] using hrun
        · simpa [hap, C.run, hb, he, hptr, reset2Heap, reset2Pre, resetPre, resetKeepState, resetKeepStream,
            inflateResetState, inflateResetStream, setI, putInflate, i2u, i2ul, hcast, hn32, hnat, he', dropWindow, freeWin] using hrun

#print axioms reset2_public

end ZlibF.Spec.Public.InflateReset2Proof
