import ZlibF.Proof.«inftrees.c.canonbridge»

/-!
# The geometry of the table: the closed form `desc` against the model of the main proof
-/
namespace Zlib.Inftrees.Proofs
open Zlib.Inftrees.Canon

theorem nz_eq (f : Nat → Nat) (n : Nat) : Canon.nz (lensOf f n) = Tc f n 15 := by
  unfold Canon.nz; rw [ord_eq]; exact wsAux_length 15

theorem count_eq (f : Nat → Nat) (n l : Nat) : (lensOf f n).count l = cnt f n l := by
  unfold lensOf cnt fl
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  rfl

theorem offL_eq (f : Nat → Nat) (n : Nat) : ∀ l, Canon.offL (lensOf f n) (l + 1) = Tc f n l
  | 0 => by simp [Canon.offL_one, Tc]
  | l + 1 => by
    rw [Canon.offL_succ, offL_eq f n l]
    simp [count_eq, Tc]

theorem cntGE_eq (f : Nat → Nat) (n a : Nat) {l : Nat} (hl : 1 ≤ l) :
    Canon.cntGE (lensOf f n) a l = rem f n a l := by
  unfold Canon.cntGE rem
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [offL_eq, offL_eq]
  simp

theorem grp_eq_pre (f : Nat → Nat) (n R : Nat) {j : Nat} (hj : j < Tc f n 15) (hR : R ≤ lenAt f n j) :
    Canon.grp (lensOf f n) R j = pre f n R j := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hj
  unfold Canon.grp pre
  rw [K_eq f n j hj]
  have e : 2 ^ (15 - R) = 2 ^ (15 - lenAt f n j) * 2 ^ (lenAt f n j - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm (val f n j) _, Nat.mul_div_mul_left _ _ (Nat.pow_pos (by omega))]

theorem startsAt_iff (f : Nat → Nat) (n R : Nat) {i : Nat} (hi : i + 1 < Tc f n 15) :
    Canon.startsAt (lensOf f n) R i ↔
      (R < lenAt f n (i + 1) ∧ (lenAt f n i ≤ R ∨ pre f n R (i + 1) ≠ pre f n R i)) := by
  unfold Canon.startsAt
  rw [L_eq f n hi, L_eq f n (show i < Tc f n 15 by omega)]
  by_cases hs : lenAt f n i ≤ R
  · simp [hs]
  · have hR1 : R < lenAt f n (i + 1) ∨ lenAt f n (i + 1) ≤ R := by omega
    simp only [hs, false_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rwa [grp_eq_pre f n R hi (by omega), grp_eq_pre f n R (show i < Tc f n 15 by omega) (by omega)] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [grp_eq_pre f n R hi (by omega), grp_eq_pre f n R (show i < Tc f n 15 by omega) (by omega)]
      exact h2

theorem look_eq (f : Nat → Nat) (n a R mx : Nat) (hR1 : 1 ≤ R) :
    ∀ F c (left : Int), mx - R - c ≤ F →
      Canon.look (lensOf f n) a R mx c left F = (SL (rem f n a) R mx c left).1
  | 0, c, left, h => by
    have : mx ≤ R + c := by omega
    rw [SL_ge this]; rfl
  | F + 1, c, left, h => by
    by_cases hc : c + R < mx
    · rw [SL_lt (show R + c < mx by omega)]
      simp only [Canon.look, hc, ite_true]
      rw [cntGE_eq f n a (show 1 ≤ c + R by omega), show c + R = R + c by omega]
      by_cases hl : left - (rem f n a (R + c) : Int) ≤ 0
      · simp [hl]
      · simp only [hl, ite_false]
        rw [look_eq f n a R mx hR1 F (c + 1) _ (by omega)]
        rw [Int.mul_comm]
    · rw [SL_ge (show mx ≤ R + c by omega), Canon.look]
      simp [hc]

theorem width_eq (f : Nat → Nat) (n R : Nat) {a : Nat} (hR1 : 1 ≤ R) (ha : a < Tc f n 15)
    (hmx : lenAt f n a ≤ mxl f n) (hRa : R < lenAt f n a) (h15 : mxl f n ≤ 15) :
    Canon.width (lensOf f n) a R (mxl f n) = currOf f n R a := by
  unfold Canon.width currOf
  rw [L_eq f n ha, look_eq f n a R (mxl f n) hR1 16 _ _ (by omega)]

theorem desc_succ_of_starts (ls : List Nat) (R mx i : Nat) (h : Canon.startsAt ls R i) :
    Canon.desc ls R mx (i + 1) =
      ⟨R, Canon.width ls (i + 1) R mx, (Canon.desc ls R mx i).base + 2 ^ (Canon.desc ls R mx i).curr,
        (Canon.desc ls R mx i).used + 2 ^ Canon.width ls (i + 1) R mx, Canon.rev R (Canon.grp ls R (i + 1))⟩ := by
  simp [Canon.desc, h]

theorem desc_succ_of_not (ls : List Nat) (R mx i : Nat) (h : ¬ Canon.startsAt ls R i) :
    Canon.desc ls R mx (i + 1) = Canon.desc ls R mx i := by
  simp [Canon.desc, h]

end Zlib.Inftrees.Proofs
