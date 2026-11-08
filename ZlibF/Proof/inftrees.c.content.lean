import ZlibF.Spec.InflateTableContent
import ZlibF.Proof.«inftrees.c.content.geometry»

/-!
# inftrees.c: retain constructed contents through the actual wrappers

Companion proofs strengthen the existing execution interfaces. The translated
function and original theorem statements remain unchanged. The main loop's
existing write invariant supplies contents after its geometry is discharged.
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec
set_option autoImplicit false

private theorem rejected_content_wp
    {type : UInt32} {f : Nat → Nat} {n oc : Nat} {rc : CodeRef}
    {value : Int32 × CodePtr × UInt32} {h : Heap}
    {Q : (Int32 × CodePtr × UInt32) → Heap → Prop}
    (reject : value.1 ≠ 0) (previous : Wp (pure value) h Q) :
    Wp (pure value) h (fun r after => Q r after ∧ TableContent type f n rc oc r after) := by
  obtain ⟨result, after, run, post⟩ := previous
  change Except.ok (value, h) = Except.ok (result, after) at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
  exact ⟨value, h, rfl, post, fun success => False.elim (reject success)⟩

theorem itB_content_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max min root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmax : max.toNat = mxl P.f codes.toNat) (hpos : 0 < Tc P.f codes.toNat 15)
    (hmin : min.toNat = lenAt P.f codes.toNat 0)
    (hr1 : 1 ≤ root.toNat) (hr0 : lenAt P.f codes.toNat 0 ≤ root.toNat) (hrm : root.toNat ≤ mxl P.f codes.toNat)
    (hrC : type = CODES → root.toNat = mxl P.f codes.toNat) :
    Wp (itB type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max min root) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧
        TableContent type P.f codes.toNat rc oc r h') := by
  unfold itB
  apply Wp.bind' (kraft_loop P.f codes.toNat count hcs hcc h)
  rintro ⟨left, bad, len⟩ h' ⟨rfl, hk⟩
  dsimp only at hk ⊢
  by_cases hbad : bad = true
  · rw [if_pos hbad]
    have hnf : ¬ Fits P.f codes.toNat := by
      rcases hk with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd (hbad.symm.trans h1) (by decide)
    apply rejected_content_wp (by change (-1 : Int32) ≠ 0; decide)
    exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
      fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
      fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ hacc => hnf hacc.1⟩
  · rw [if_neg hbad]
    have hbad' : bad = false := by simpa using hbad
    obtain ⟨hfit, hleft⟩ : Fits P.f codes.toNat ∧ left.toInt = 2 ^ 15 - (Kc P.f codes.toNat 15 : Int) := by
      rcases hk with ⟨h1, _⟩ | ⟨_, h2, h3⟩
      · exact absurd h1 hbad
      · exact ⟨h2, h3⟩
    have hK15 := hfit 15 (by omega) (by omega)
    by_cases hg : (decide (left > 0) && (type == CODES || max != 1)) = true
    · rw [if_pos hg]
      have hgl' : left > 0 ∧ (type == CODES || max != 1) = true := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hg
      have hl' : 0 < left.toInt := by
        have := Int32.lt_iff_toInt_lt.mp hgl'.1; simpa using this
      have hnacc : ¬ Acc type P.f codes.toNat := by
        rintro ⟨_, h2 | h2 | ⟨hnc, hm1, _⟩⟩
        · omega
        · omega
        · have hmax1 : max = 1 := UInt32.toNat_inj.mp (by rw [hmax, hm1]; rfl)
          have := hgl'.2
          simp [hnc, hmax1] at this
      apply rejected_content_wp (by change (-1 : Int32) ≠ 0; decide)
      exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
        fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
        fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ => hnacc⟩
    · rw [if_neg hg]
      have hend : Kc P.f codes.toNat 15 = 2 ^ 15 ∨ (mxl P.f codes.toNat = 1 ∧ Tc P.f codes.toNat 15 = 1 ∧ type ≠ CODES) := by
        by_cases hl : left > 0
        · right
          have hl' : 0 < left.toInt := by
            have := Int32.lt_iff_toInt_lt.mp hl; simpa using this
          have hnc1 : type ≠ CODES := fun ht => hg (by simp [hl, ht])
          have hnc2 : max = 1 := Classical.byContradiction (fun hne => hg (by simp [hl, hne]))
          have hm1 : mxl P.f codes.toNat = 1 := by
            have := congrArg UInt32.toNat hnc2; rw [hmax] at this; simpa using this
          have hlt : Kc P.f codes.toNat 15 < 2 ^ 15 := by
            have : (Kc P.f codes.toNat 15 : Int) < 2 ^ 15 := by omega
            exact_mod_cast this
          exact ⟨hm1, incomplete_one hpos hfit hlt hm1, hnc1⟩
        · left
          have hl' : left.toInt ≤ 0 := by
            have : ¬ (0 < left.toInt) := fun hh => hl (Int32.lt_iff_toInt_lt.mpr (by simpa using hh))
            omega
          have : (2 ^ 15 : Int) ≤ Kc P.f codes.toNat 15 := by omega
          have : 2 ^ 15 ≤ Kc P.f codes.toNat 15 := by exact_mod_cast this
          omega
      have hn288 : codes.toNat ≤ 288 := by
        rcases P.hty with ht | ht | ht
        · have := (P.hcodes ht).1; omega
        · exact P.hlens ht
        · have := P.hdists ht; omega
      rw [seta_eq (by simp)]
      rw [M_pure_bind]
      apply Wp.bind' (offs_loop P.f codes.toNat hn288 count hcs hcc _)
      rintro ⟨len2, offs⟩ h' ⟨rfl, hos, hoj⟩
      dsimp only at hos hoj ⊢
      apply Wp.bind' (sort_loop P.f codes.toNat hn288 rl rw P.hne ol ow P.la P.wa codes rfl _ P.hgl P.hgw P.hla
        (fun k => rfl) P.hf15 P.hwa offs hos hoj)
      rintro ⟨sym, offs'⟩ h2 ⟨hsym, wa1, rfl, hinv⟩
      dsimp only at hinv ⊢
      obtain ⟨_, _, hsz1, hfr1, hcont1⟩ := hinv
      have key : ∀ (base extra : Array UInt16) (match_ : UInt32),
          (type = CODES → match_ = 20) →
          (type = LENS → base = lbase ∧ extra = lext ∧ match_ = 257) →
          (type = DISTS → base = dbase ∧ extra = dext ∧ match_ = 0) →
          Wp (itTail type (Ptr.ref rl ol) (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max min root left base extra match_)
            (Space.put h' rw wa1)
            (fun r h2 => (Result h' rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h2 ∧
              RetInfo type P.f codes.toNat r) ∧
        TableContent type P.f codes.toNat rc oc r h2) := by
        intro base extra match_ hC hL hD
        let c0 : Ctx := { type, lens := Ptr.ref rl ol, work := Ptr.ref rw ow, table := Ptr.ref rc oc, root, max, base, extra, match_ }
        let e : Env :=
          { c := c0,
            f := P.f, n := codes.toNat, R := root.toNat, cap := capOf type, rc := rc, oc := oc, «rw» := «rw», ow := ow,
            rl := rl, ol := ol, hb := Space.put h' rw wa1, la := P.la, wa := wa1,
            h_table := rfl, h_lens := rfl, h_work := rfl, h_ro := P.hro,
            h_live := ⟨P.ca, by rw [cget_put_word]; exact P.hgc⟩,
            h_get_la := by rw [wget_put_ne P.hne]; exact P.hgl,
            h_get_wa := wget_put_self P.hgw wa1, h_f := fun k => rfl, h_la := P.hla, h_f15 := P.hf15,
            h_wa := by rw [hsz1]; exact P.hwa,
            h_wcont := fun i hi => by
              have hb := lenAt_bounds (f := P.f) (n := codes.toNat) hi
              have blk := (lenAt_eq_iff (f := P.f) (n := codes.toNat) (l := lenAt P.f codes.toNat i) hb.1 hb.2 hi).mp rfl
              have hlt : i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1) < cnt P.f codes.toNat (lenAt P.f codes.toNat i) := by
                have := Tc_succ' (f := P.f) (n := codes.toNat) hb.1
                omega
              have := hcont1 (lenAt P.f codes.toNat i) (i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1)) hb.1 hb.2 hlt
              rw [show ow + Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1) + (i - Tc P.f codes.toNat (lenAt P.f codes.toNat i - 1)) = ow + i by omega] at this
              rw [this, ws_getD hi],
            h_n := hn288, h_root := rfl, h_max := hmax, h_R1 := hr1, h_Rmx := hrm, h_R0 := hr0, h_pos := hpos,
            h_fits := hfit, h_end := hend, h_type := P.hty, h_cap := rfl,
            h_codes := fun ht => ⟨by
                have hall := (P.hcodes ht).2.1
                show lenAt P.f codes.toNat (Tc P.f codes.toNat 15 - 1) ≤ 7
                unfold lenAt
                exact hall _ (ws_getD_lt (by omega)), hrC ht, (P.hcodes ht).1, hC ht⟩,
            h_lens' := fun ht => ⟨hn288, hL ht⟩, h_dists := fun ht => ⟨(P.hdists ht), hD ht⟩ }
        have hcnt0 : CountOK e count 0 := ⟨hcs, fun l h1 h2 => by
          rw [hcc l h1 h2]; exact (rem_zero (f := P.f) (n := codes.toNat) h1).symm⟩
        have hhc : e.hc P.ca = Space.put h' rw wa1 :=
          cput_self (by rw [cget_put_word]; exact P.hgc)
        have := itTail_wp e P.ca count bits min left hcnt0 hmin P.hca
        rw [hhc] at this
        refine Wp.mono this ?_
        rintro r h3 ⟨ca', rfl, hf, hr, hrne⟩
        constructor
        · have hacc : Acc type P.f codes.toNat := by
            refine ⟨hfit, ?_⟩
            rcases hend with h | ⟨a, b, c⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr ⟨c, a, b⟩)
          have hr01 : r.1 = 0 ∨ r.1 = 1 := by
            rcases hr with ⟨h0, _⟩ | ⟨h1, _⟩
            · exact Or.inl h0
            · exact Or.inr h1
          refine ⟨⟨wa1, ca', rfl, hsz1, hf.1.trans rfl, hfr1, hf.2, ?_⟩,
            fun _ => hacc, fun h1 => ⟨hacc, hrne.1 h1⟩, fun hm => ?_⟩
          · rcases hr with ⟨h0, u, hu, hr2, _⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨h0, u, hu, hr2⟩
            · exact Or.inr ⟨Or.inl h1, h2, h3⟩
          · exfalso
            rcases hr01 with h0 | h0 <;> rw [h0] at hm <;> exact absurd hm (by decide)
        · intro success
          obtain ⟨written, links⟩ := (hrne.2 success).established
          rcases hr with ⟨_, used, bounded, endPointer, rootBits⟩ | ⟨bad, _, _⟩
          · right
            refine ⟨hpos, e, ca', rfl, rfl, ?_, rfl, rfl, rfl, ?_, written, links⟩
            · exact congrArg UInt32.toNat rootBits.symm
            · exact cget_put_self (Classical.choose_spec e.h_live) e.h_ro ca'
          · have : (1 : Int32) = 0 := bad.symm.trans success
            contradiction
      rcases P.hty with ht | ht | ht
      · subst ht
        rw [if_pos (by decide)]
        exact key #[] #[] 20 (fun _ => rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      · subst ht
        rw [if_neg (by decide), if_pos (by decide)]
        exact key lbase lext 257 (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩) (fun h => absurd h (by decide))
      · subst ht
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        exact key dbase dext 0 (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩)

theorem itA_content_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmaxq : (Tc P.f codes.toNat 15 = 0 ∧ max.toNat = 0) ∨ (0 < Tc P.f codes.toNat 15 ∧ max.toNat = mxl P.f codes.toNat))
    (hroot : root.toNat ≤ max.toNat) (hrC : type = CODES → root.toNat = max.toNat) :
    Wp (itA type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max root) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧
        TableContent type P.f codes.toNat rc oc r h') := by
  unfold itA
  by_cases hm0 : (max == 0) = true
  · rw [if_pos hm0]
    have hcap2 := capOf_ge type
    have hca := P.hca
    show Wp (do Ptr.store (Ptr.ref rc oc) (⟨64, 1, 0⟩ : Code)
                let table ← Ptr.add (Ptr.ref rc oc) 1
                Ptr.store table (⟨64, 1, 0⟩ : Code)
                let table ← Ptr.add table 1
                return ((0 : Int32), table, (1 : UInt32))) _ _
    apply Wp.bind' (Q := fun _ h2 => h2 = Space.put h rc (P.ca.set! oc ⟨64, 1, 0⟩))
      (wpC_store h rc P.ca oc _ P.hgc P.hro (by omega))
    rintro _ h1 rfl
    have hg1 := cget_put_self P.hgc P.hro (P.ca.set! oc (⟨64, 1, 0⟩ : Code))
    apply Wp.bind' (Q := fun q h2 => q = Ptr.ref rc (oc + 1) ∧ h2 = Space.put h rc (P.ca.set! oc ⟨64, 1, 0⟩))
      (wpC_add _ rc _ oc 1 hg1 (by rw [Array.size_set!]; omega))
    rintro q h2 ⟨rfl, rfl⟩
    apply Wp.bind' (Q := fun _ h3 => h3 = Space.put h rc ((P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩))
      (by
        have := wpC_store _ rc _ (oc + 1) (⟨64, 1, 0⟩ : Code) hg1 P.hro (by rw [Array.size_set!]; omega)
        refine Wp.mono this ?_
        intro _ h3 hh; rw [hh, cput_put])
    rintro _ h3 rfl
    have hg2 := cget_put_self P.hgc P.hro ((P.ca.set! oc (⟨64, 1, 0⟩ : Code)).set! (oc + 1) (⟨64, 1, 0⟩ : Code))
    apply Wp.bind' (Q := fun q h4 => q = Ptr.ref rc (oc + 1 + 1) ∧ h4 = Space.put h rc ((P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩))
      (wpC_add _ rc _ (oc + 1) 1 hg2 (by rw [Array.size_set!, Array.size_set!]; omega))
    rintro q h4 ⟨rfl, rfl⟩
    have hT0 : Tc P.f codes.toNat 15 = 0 := by
      have hm0' : max.toNat = 0 := by
        have : max = 0 := by simpa using hm0
        rw [this]; rfl
      rcases hmaxq with ⟨a, _⟩ | ⟨a, b⟩
      · exact a
      · have := lenAt_bounds (f := P.f) (n := codes.toNat) a
        have h3 : mxl P.f codes.toNat = lenAt P.f codes.toNat (Tc P.f codes.toNat 15 - 1) := rfl
        have := lenAt_bounds (f := P.f) (n := codes.toNat) (show Tc P.f codes.toNat 15 - 1 < Tc P.f codes.toNat 15 by omega)
        omega
    have hacc : Acc type P.f codes.toNat := ⟨fits_of_zero hT0, Or.inr (Or.inl hT0)⟩
    apply Wp.pure'
    constructor
    · refine ⟨⟨P.wa, (P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩, ?_, rfl, ?_, fun _ _ => rfl, ?_, Or.inl ⟨rfl, 2, hcap2, rfl⟩⟩,
        fun _ => hacc, fun h => absurd (show (0 : Int32) = 1 from h) (by decide),
        fun h => absurd (show (0 : Int32) = -1 from h) (by decide)⟩
      · rw [wput_self P.hgw]
      · simp [Array.size_set!]
      · intro x hx
        have h1 : oc + 1 ≠ x := by omega
        have h2 : oc ≠ x := by omega
        rw [getElem?_set!_ne h1, getElem?_set!_ne h2]
    · intro _
      left
      refine ⟨hT0, rfl, rfl, _, hg2, ?_, ?_⟩
      · rw [getElem?_set!_ne (by omega : oc + 1 ≠ oc)]
        exact getElem?_set!_self (by omega)
      · exact getElem?_set!_self (by rw [Array.size_set!]; omega)
  · rw [if_neg hm0]
    have hm0' : max.toNat ≠ 0 := fun h0 => hm0 (by
      have : max = 0 := UInt32.toNat_inj.mp (by rw [h0]; rfl)
      simp [this])
    obtain ⟨hpos, hmx⟩ : 0 < Tc P.f codes.toNat 15 ∧ max.toNat = mxl P.f codes.toNat := by
      rcases hmaxq with ⟨_, h2⟩ | h2
      · exact absurd h2 hm0'
      · exact h2
    obtain ⟨hl1, hl2⟩ := lenAt_bounds (f := P.f) (n := codes.toNat) hpos
    have hl0mx : lenAt P.f codes.toNat 0 ≤ mxl P.f codes.toNat :=
      lenAt_mono (f := P.f) (n := codes.toNat) (show 0 ≤ Tc P.f codes.toNat 15 - 1 by omega) (by omega)
    apply Wp.bind' (min_loop P.f codes.toNat count hcs hcc max hmx hpos _)
    rintro ⟨min, brk⟩ h' ⟨rfl, hmin⟩
    dsimp only at hmin ⊢
    by_cases hr : root < min
    · rw [if_pos hr]
      have hr' : root.toNat < min.toNat := UInt32.lt_iff_toNat_lt.mp hr
      exact itB_content_wp P count max min min hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)
    · rw [if_neg hr]
      have hr' : min.toNat ≤ root.toNat := by
        have := (not_congr UInt32.lt_iff_toNat_lt).mp hr; omega
      exact itB_content_wp P count max min root hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)

theorem itTop_content_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow) :
    Wp (itTop type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow)) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧
        TableContent type P.f codes.toNat rc oc r h') := by
  have hn288 : codes.toNat ≤ 288 := by
    rcases P.hty with ht | ht | ht
    · have := (P.hcodes ht).1; omega
    · exact P.hlens ht
    · have := P.hdists ht; omega
  unfold itTop
  apply Wp.bind' (zero_loop h)
  rintro ⟨len, count⟩ h' ⟨rfl, hs, hz⟩
  dsimp only at hs hz ⊢
  apply Wp.bind' (count_loop P.f codes.toNat hn288 rl ol P.la codes rfl _ P.hgl P.hla (fun k => rfl) P.hf15 count hs hz)
  rintro ⟨sym, count2⟩ h2 ⟨rfl, hsym, hs2, hc2⟩
  dsimp only at hs2 hc2 ⊢
  have hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count2.getD l 0).toNat = cnt P.f codes.toNat l := fun l h1 h2 => hc2 l (by omega)
  apply Wp.bind' (max_loop P.f codes.toNat count2 hs2 hcc _)
  rintro ⟨max, brk⟩ h3 ⟨rfl, hmaxq⟩
  dsimp only at hmaxq ⊢
  by_cases hgt : bits > max
  · rw [if_pos hgt]
    exact itA_content_wp P count2 max max hs2 hcc hmaxq (Nat.le_refl _) (fun _ => rfl)
  · rw [if_neg hgt]
    have hle : bits.toNat ≤ max.toNat := by
      have := (not_congr UInt32.lt_iff_toNat_lt).mp hgt; omega
    exact itA_content_wp P count2 max bits hs2 hcc hmaxq hle
      (fun hC => by
        obtain ⟨_, h7, hb7⟩ := P.hcodes hC
        rcases hmaxq with ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · have := mxl_le7 (f := P.f) (n := codes.toNat) a h7
          omega)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The actual constructor retains safety, return classification and every
canonical leaf/link written by the main loop. Geometry is proved from the
constructor environment; it is not a caller premise. Empty and single-symbol
codes and all constructor error returns are included. -/
theorem inflate_table_content : Goal.inflate_table_content := by
  intro h type rl ol codes rc oc bits rw ow pre
  obtain ⟨result, after, run, old, content⟩ := itTop_content_wp pre
  refine ⟨result, after, ?_, old.1, old.2, content⟩
  rw [C.run, inflate_table_eq]
  exact run

end Zlib.Inftrees.Proofs
