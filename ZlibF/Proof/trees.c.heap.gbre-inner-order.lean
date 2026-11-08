import ZlibF.Proof.«trees.c.heap.gbre-order»

/-! # Actual reassignment steps preserve the sorted order of leaf lengths -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- One real source step either skips an internal node or assigns the
current level to a leaf. It retains the old state/count/cost conclusions
and extends the sorted scanned-leaf region on the actual returned heap. -/
theorem ws_gbInner_order {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c)
    (mc bitsv : Int32) (hmc : mc.toInt = maxc) (b : Nat) (hb1 : 1 ≤ b) (hbL : b ≤ L) (hbv : bitsv.toInt = b)
    (n hc : Nat) (nI hI : Int32) (hnI : nI.toInt = n) (hhI : hI.toInt = hc) (hn : 1 ≤ n) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 hc b n e)
    (ordered : ReOrdered (Hn e0) (curL (tk.arr e)) maxc hc) :
    WS h0 id (gbInner (Sp id) (Ptr.ref (tk.ref id) 0) mc bitsv (nI, hI)) e (fun r e' =>
      ∃ (hc' n' : Nat), r.1.toInt = (n' : Int) ∧ r.2.toInt = (hc' : Int) ∧ hc' < hc ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b n' e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc') := by
  obtain ⟨Tc, O, rfl, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ := hR
  rw [tk_arr_mkP2] at ordered
  have PS := ctx.shape
  have current : ReSt tk e0 hm J maxc L xb c opt0 hc b n (mkP2 tk e0 Tc O) :=
    ⟨Tc, O, rfl, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩
  have range := ReSt.processed_range PS hbL current
  simp only [tk_arr_mkP2] at range
  have hm_eq := PS.hm_eq
  have hsz := ctx.hsz
  have hL15 := ctx.L15
  have hL1 := ctx.L1
  have hcb : c b ≤ 600 := by
    have h1 := le_rs (F := c) (n := L + 1) (i := b) (by omega)
    have h2 := nLeaves_le ctx.shape
    have h3 := ctx.shape.maxc_lt
    have h4 := ctx.nc; have h5 := ctx.tsz
    rw [ctx.ctot] at h1; omega
  have hut : 1 ≤ utot (Hn e0) hm maxc J hc := by
    have := stot_utot (Hn e0) hm maxc J hc
    have := Aab_le c L b hbL
    have := ctx.ctot
    omega
  have hcp : hm + 2 ≤ hc := by
    by_cases hx : hm + 2 ≤ hc
    · exact hx
    · exfalso
      have : utot (Hn e0) hm maxc J hc = 0 := rs_eq_zero (fun i _ => by rw [if_neg (fun h => by omega)])
      omega
  have hp573 : hc - 1 < 573 := by omega
  have hnn := ctx.hnn (hc - 1) (by omega) hp573
  have hnode : Hn e0 (hc - 1) < elems + J := by
    rcases PS.kind (hc - 1) (by omega) hp573 with h1 | h1
    · have := PS.maxc_lt; omega
    · omega
  have hnc' := ctx.nc
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hinj : ∀ i, i < 2 * J → hc ≤ hm + 1 + i → Hn e0 (hm + 1 + i) ≠ Hn e0 (hc - 1) := by
    intro i hi h1 e
    have := PS.inj (hm + 1 + i) (hc - 1) (by omega) (by omega) (by omega) hp573 e; omega
  unfold gbInner
  simp only []
  refine WS.bind' (ws_isub hI 1 (by omega) (by omega)) fun h' e1 ⟨hh', he1⟩ => ?_
  subst e1
  have hh'v : h'.toInt = (hc - 1 : Nat) := by omega
  refine WS.bind' (ws_heapAt h' (by omega) (by rw [mkP2_heap]; omega)) fun m e1 ⟨hmv, he1⟩ => ?_
  subst e1
  have hmI : m.toInt = (Hn e0 (hc - 1) : Int) := by
    rw [mkP2_heap] at hmv
    have : h'.toInt.toNat = hc - 1 := by omega
    rw [this] at hmv; rw [hmv]; unfold Hn; omega
  have hcJ : hc ≤ hm + 1 + 2 * J := by omega
  -- the common ending: isub n 1, then the result
  have fin : ∀ (Tn : Array CtData) (On : UInt64), Tn.size = (tk.arr e0).size →
      On = opt0 + UInt64.ofNat (costP (Hn e0) hm maxc (frn (tk.arr e0)) (curL Tn) xb (2 * J)) →
      (curL Tn = fun v => if v = Hn e0 (hc - 1) then b else curL Tc v) →
      (∀ v : Nat, (Tn[v]!).fc = ((tk.arr e0)[v]!).fc) →
      (∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn e0 q ≠ v) → (Tn[v]!).dl = ((tk.arr e0)[v]!).dl) →
      Hn e0 (hc - 1) ≤ maxc →
      WS h0 id (do let r ← isub nI 1; pure (r, h')) (mkP2 tk e0 Tn On) (fun r e' =>
        ∃ (hc' n' : Nat), r.1.toInt = (n' : Int) ∧ r.2.toInt = (hc' : Int) ∧ hc' < hc ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b n' e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc') := by
    intro Tn On hTn hOn hcur hfcn houtn hleaf
    refine WS.bind' (ws_isub nI 1 (by omega) (by omega)) fun r e1 ⟨hr, he1⟩ => ?_
    subst e1
    refine WS.pure' ⟨hc - 1, n - 1, by simp only; omega, by simp only; omega, by omega,
      ⟨Tn, On, rfl, hTn, by omega, by omega, by omega, hOn, hfcn, houtn, ?_, ?_⟩, ?_⟩
    · intro x
      have hs := scnt_step (Hn e0) hm maxc J hc (curL Tc) (curL Tn) x hcp hcJ (fun i hi h1 => by
        rw [hcur]; simp [hinj i hi h1])
      rw [hs, hsc x, hcur]
      simp only [if_true, hleaf]
      by_cases e1 : b < x ∧ x ≤ L
      · rw [if_pos e1, if_pos e1]; have : x ≠ b := by omega
        simp [this, Ne.symm this]
      · rw [if_neg e1, if_neg e1]
        by_cases e2 : x = b
        · subst e2; simp; omega
        · simp [e2, Ne.symm e2]
    · rw [stot_step (Hn e0) hm maxc J hc hcp hcJ, hst, if_pos hleaf]; omega
    · simpa only [tk_arr_mkP2] using ReOrdered.assign PS hcp hc2 ordered
        (fun q lo hi leaf => (range q lo hi leaf).1) (fun v => congrFun hcur v)
  have hmt : m.toInt.toNat = Hn e0 (hc - 1) := by omega
  have hmlt : 0 ≤ m.toInt ∧ m.toInt < ((tk.arr (mkP2 tk e0 Tc O)).size : Int) := by
    rw [tk_arr_mkP2, hTs]; omega
  by_cases hleaf : Hn e0 (hc - 1) ≤ maxc
  · refine WS.ite' (fun hh => absurd hh (by omega)) (fun _ => ?_)
    refine WS.bind' (ws_getDl tk m.toInt hmlt.1 hmlt.2) fun lm e1 ⟨hlm, he1⟩ => ?_
    subst e1
    have hlm' : lm = (Tc[Hn e0 (hc - 1)]!).dl := by rw [hlm, tk_arr_mkP2, hmt]
    refine WS.ite' (fun hch => ?_) (fun hnch => ?_)
    · -- the length changes
      have hne := (bne_u32 lm bitsv (by omega) (by omega)).mp hch
      refine WS.bind' (ws_getFc tk m.toInt hmlt.1 hmlt.2) fun fm e1 ⟨hfm, he1⟩ => ?_
      subst e1
      have hfm' : fm.toNat = frn (tk.arr e0) (Hn e0 (hc - 1)) := by
        rw [hfm, tk_arr_mkP2, hmt, hfc]; rfl
      refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
      subst e1
      rw [optlen_mkP2]
      refine WS.bind' (ws_setDl tk m.toInt (i2us bitsv) hmlt.1 (by rw [tk_arr_mkP2, hTs]; omega)) fun _ e1 he1 => ?_
      subst e1
      rw [setArr_mkP2, tk_arr_mkP2, hmt, i2us_eq bitsv (by omega) (by omega)]
      have hbn : bitsv.toInt.toNat = b := by omega
      rw [hbn]
      have hvT : Hn e0 (hc - 1) < Tc.size := by omega
      have hcur := curL_setLen Tc (Hn e0 (hc - 1)) b hvT (by omega)
      refine fin (setLen Tc (Hn e0 (hc - 1)) b) _ (by unfold setLen; rw [size_set!]; exact hTs) ?_ hcur ?_ ?_ hleaf
      · simp only [mkP2_opt_len]
        rw [hcur, i2ul_eq bitsv (by omega) (by omega), hbn, u16_u64 lm, u16_u64 fm, hfm', hlm', hO]
        have hcs := costP_set (Hn e0) hm maxc J (frn (tk.arr e0)) (curL Tc) xb (hc - 2 - hm) b (by omega)
          (by have : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
              rw [this]; exact hleaf)
          (fun i hi hne => by
            have : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
            rw [this]
            intro e; have := PS.inj (hm + 1 + i) (hc - 1) (by omega) (by omega) (by omega) hp573 e; omega)
        have e5 : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
        rw [e5] at hcs
        have := opt_upd opt0 (costP (Hn e0) hm maxc (frn (tk.arr e0)) (curL Tc) xb (2 * J))
          (costP (Hn e0) hm maxc (frn (tk.arr e0)) (fun v => if v = Hn e0 (hc - 1) then b else curL Tc v) xb (2 * J))
          (frn (tk.arr e0) (Hn e0 (hc - 1))) (curL Tc (Hn e0 (hc - 1))) b hcs
        have e6 : curL Tc (Hn e0 (hc - 1)) = (Tc[Hn e0 (hc - 1)]!).dl.toNat := rfl
        rw [e6] at this; rw [this]
      · intro v
        unfold setLen; rw [getD_set Tc _ v _ hvT]
        by_cases e : v = Hn e0 (hc - 1)
        · subst e; simp [hfc]
        · simp [e, hfc v]
      · intro v hv
        unfold setLen; rw [getD_set Tc _ v _ hvT, if_neg]
        · exact hout v hv
        · intro e; exact hv (hc - 1) (by omega) hp573 e.symm
    · have heq : lm.toNat = b := by
        have hh : lm.toNat = bitsv.toInt.toNat := by
          by_cases e : lm.toNat = bitsv.toInt.toNat
          · exact e
          · exact absurd ((bne_u32 lm bitsv (by omega) (by omega)).mpr e) hnch
        omega
      have hcm : curL Tc (Hn e0 (hc - 1)) = b := by unfold curL; rw [← hlm']; exact heq
      refine fin Tc O hTs hO ?_ hfc hout hleaf
      funext v
      by_cases e : v = Hn e0 (hc - 1)
      · subst e; simp [hcm]
      · simp [e]
  · refine WS.ite' (fun _ => ?_) (fun hh => absurd (by omega) hh)
    refine WS.pure' ⟨hc - 1, n, hnI, hh'v, by omega,
      ⟨Tc, O, rfl, hTs, by omega, by omega, hnc, hO, hfc, hout, ?_, ?_⟩, ?_⟩
    · intro x
      have hs := scnt_step (Hn e0) hm maxc J hc (curL Tc) (curL Tc) x hcp hcJ (fun i hi h1 => rfl)
      have hz : ¬ (Hn e0 (hc - 1) ≤ maxc ∧ curL Tc (Hn e0 (hc - 1)) = x) := fun h => hleaf h.1
      rw [hs, hsc x, if_neg hz, Nat.add_zero]
    · rw [stot_step (Hn e0) hm maxc J hc hcp hcJ, hst, if_neg hleaf]; rfl
    · simpa only [tk_arr_mkP2] using ReOrdered.skip ordered (by omega)


end Zlib.Trees.Proofs
