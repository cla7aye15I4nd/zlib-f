import ZlibF.Math.InflateDefaultTableBudget
import ZlibF.Proof.«inftrees.c.content.tail»
import ZlibF.Proof.«inftrees.c.content.geometry»
import ZlibF.Proof.«inftrees.c.decode.invariant»

namespace Zlib.Inftrees.Proofs.BudgetExecution
open C Zlib.Inftrees Zlib.Inftrees.Canon Zlib.Inftrees.Spec
open Zlib.Inftrees.Proofs.DefaultBudget
set_option autoImplicit false

private theorem bind_return {α β : Type} {m : M α} {f : α → M β}
    {h after : Heap} {value : β} (run : (m >>= f) h = .ok (value, after)) :
    ∃ a middle, m h = .ok (a, middle) ∧ f a middle = .ok (value, after) := by
  cases first : m h with
  | error fault => simp only [bind_app, first] at run; contradiction
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa only [bind_app, first] using run⟩

/-- The translated capacity test is false at every proven in-budget value. -/
theorem tooBig_false_of_budget (e : Env) {used : UInt32} (bound : used.toNat ≤ e.cap) :
    tooBig e.c.type used = false := by
  have capacity := e.h_cap
  rcases e.h_type with type | type | type
  · rw [type]
    simp [tooBig, CODES, LENS, DISTS]
  · rw [type] at capacity ⊢
    simp [CODES, LENS, DISTS] at capacity
    have small : ¬ used > ENOUGH_LENS.toUInt32 := by
      rw [gt_iff_lt, UInt32.lt_iff_toNat_lt]
      change ¬ 852 < used.toNat
      omega
    simp [tooBig, LENS, DISTS, small]
  · rw [type] at capacity ⊢
    simp [CODES, LENS, DISTS] at capacity
    have small : ¬ used > ENOUGH_DISTS.toUInt32 := by
      rw [gt_iff_lt, UInt32.lt_iff_toNat_lt]
      change ¬ 592 < used.toNat
      omega
    simp [tooBig, LENS, DISTS, small]

/-- At a real secondary-table opening, the tested used value is exactly
the next actual Canon descriptor; its mathematical bound excludes refusal. -/
theorem openBody_no_refusal (e : Env) (i : Nat) (s : TS) (ca : Array Code)
    (h : OB e i s ca) (hx : DescB e i s ∧ Cont e (i + 1) i ca)
    (hst : Canon.startsAt e.ls e.R i)
    (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap)
    {result : TS} {after : Heap} (run : openBody e.c s (e.hc ca) = .ok (result, after)) :
    result.exit ≠ 2 := by
  obtain ⟨hxD, hxC⟩ := hx
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, hdrop, halign⟩ := h
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hlmx : e.l (i + 1) ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i + 1 ≤ Tc e.f e.n 15 - 1 by
    have : i + 1 < e.m := hi
    unfold Env.m at this; omega) (by have := e.h_pos; omega)
  have hR1 := e.h_R1
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  subst hnext
  obtain ⟨⟨k', hk'1, hk'2⟩, hcurrD, husedD⟩ := hxD
  have hkb : k = (e.D i).base := by
    have := Ptr.ref.inj hk'1
    have : k = k' := by omega
    rw [this]; exact hk'2
  unfold openBody at run
  obtain ⟨q, middle, pointer, pointerFacts⟩ := wp_add e ca (e.oc + k) min.toNat (by rw [hmin]; omega)
  obtain ⟨rfl, rfl⟩ := pointerFacts
  rw [bind_app, pointer] at run
  dsimp only at run
  have hsubl : (len - drop).toNat = e.l (i + 1) - e.R := by rw [u32_sub (by omega), hlen, hdrop]
  have hcl31 : (len - drop).toNat < 31 := by omega
  rw [shl1i32_eq hcl31] at run
  simp only [bind_app, pure_app] at run
  have hl0 : (1 <<< (len - drop).toInt32 : Int32).toInt = 2 ^ (len - drop).toNat := shl1i32_toInt hcl31
  obtain ⟨triple, loopHeap, loopRun, loopFacts⟩ :=
    size_loop e (i + 1) count drop e.c.max (len - drop) _ (e.hc ca) hcnt hdrop e.h_max hRl hsubl hl0 hi
  obtain ⟨cs, ls, bs⟩ := triple
  obtain ⟨rfl, hcs⟩ := loopFacts
  change cwhile
    (fun x : UInt32 × Int32 × Bool => pure (!x.2.2 && decide (x.1 + drop < e.c.max), x.1, x.2.1, x.2.2))
    (fun x : UInt32 × Int32 × Bool => do
      let cc ← geta count (x.1 + drop).toNat
      let left ← chk32 (x.2.1.toInt - cc.toNat)
      if left ≤ 0 then pure (x.1, left, true)
      else do
        let left ← chk32 (left.toInt * 2)
        pure (x.1 + 1, left, x.2.2))
    (len - drop, 1 <<< (len - drop).toInt32, false) (e.hc ca) = .ok ((cs, ls, bs), e.hc ca) at loopRun
  rw [loopRun] at run
  dsimp only at run hcs
  have originalMax : lenAt e.f e.n (i + 1) ≤ mxl e.f e.n := hlmx
  have csMax : e.R + cs.toNat ≤ e.mx := by
    have bounds := block_bound (f := e.f) (n := e.n) (R := e.R) (i0 := i + 1) hi hRl halign
    have limit : e.R + currOf e.f e.n e.R (i + 1) ≤ e.mx := bounds.2.1
    rw [← hcs] at limit
    exact limit
  have hcs32 : cs.toNat < 32 := by omega
  rw [shl32_eq hcs32] at run
  simp only [bind_app, pure_app] at run
  have hu : ((1 : UInt32) <<< cs).toNat = 2 ^ cs.toNat := u32_shl1 hcs32
  have width : Canon.width e.ls (i + 1) e.R e.mx = cs.toNat := by
    rw [hcs]
    exact width_eq e.f e.n e.R hR1 hi (by omega) hRl hmxle
  have nextDesc := desc_succ_of_starts e.ls e.R e.mx i hst
  have nextBound := budget (i + 1) hi
  change (Canon.desc e.ls e.R e.mx (i + 1)).used ≤ e.cap at nextBound
  rw [nextDesc] at nextBound
  dsimp only at nextBound
  change (e.D i).used + 2 ^ Canon.width e.ls (i + 1) e.R e.mx ≤ e.cap at nextBound
  rw [width, ← husedD] at nextBound
  have capacity : (used + (1 <<< cs)).toNat ≤ e.cap := by
    rw [u32_add (a := used) (b := 1 <<< cs) (by
      have cap := e.h_cap
      have maxCap : e.cap ≤ 852 := by
        rcases e.h_type with t | t | t <;> simp [t, CODES, LENS, DISTS] at cap <;> omega
      have power : 2 ^ cs.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
      omega), hu]
    exact nextBound
  have guard := tooBig_false_of_budget e capacity
  simp only [guard, Bool.false_eq_true, ite_false] at run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  obtain ⟨_, _, _, run⟩ := bind_return run
  change Except.ok (_, _) = Except.ok (result, after) at run
  cases run
  simpa only [hex] using (show (0 : UInt8) ≠ 2 by decide)

#print axioms tooBig_false_of_budget
#print axioms openBody_no_refusal

theorem openBody_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap)
    (i : Nat) (s : TS) (ca : Array Code) (h : OB e i s ca)
    (hx : DescB e i s ∧ Cont e (i + 1) i ca) (hst : Canon.startsAt e.ls e.R i) :
    Wp (openBody e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
      ((s'.exit = 0 ∧ MI e (i + 1) s' ca' ∧ Ex e (i + 1) s' ca') ∨
        (s'.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size)) ∧ s'.exit ≠ 2) := by
  obtain ⟨result, after, run, ca', heap, frame, post⟩ := openBody_wp e i s ca h hx hst
  exact ⟨result, after, run, ca', heap, frame, post, openBody_no_refusal e i s ca h hx hst budget run⟩

theorem jp2_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap) (i : Nat) (s : TS) (ca : Array Code) (h : MI2 e i s ca) (hx : Ex1 e i s ca) :
    Wp (jp2 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
      ((s'.exit = 0 ∧ MI e (i + 1) s' ca' ∧ Ex e (i + 1) s' ca') ∨
        (s'.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size)) ∧ s'.exit ≠ 2) := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, hTab, hmin⟩ := h
  have hTab' := hTab
  obtain ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hphA, hphB⟩ := hTab'
  have hmono : e.l i ≤ e.l (i + 1) := lenAt_mono (f := e.f) (n := e.n) (Nat.le_succ i) hi
  have hroot := e.h_root
  have hR1 := e.h_R1
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hlmx : e.l (i + 1) ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i + 1 ≤ Tc e.f e.n 15 - 1 by
    have : i + 1 < e.m := hi
    unfold Env.m at this; omega) (by have := e.h_pos; omega)
  have hmask' : (s.huff &&& s.mask).toNat = rev e.R (e.p (i + 1)) ∨ ¬ (e.R ≤ e.l (i + 1)) := by
    by_cases hle : e.R ≤ e.l (i + 1)
    · left
      rw [u32_and_mod (k := e.R) (by rw [hmask]), hhuff]
      exact huff_low (f := e.f) (n := e.n) (R := e.R) (j := i + 1) hle
    · right; exact hle
  unfold jp2
  by_cases hRl : e.R < e.l (i + 1)
  · have hmk : (s.huff &&& s.mask).toNat = rev e.R (e.p (i + 1)) := by
      rcases hmask' with h | h
      · exact h
      · omega
    have hpl : e.p (i + 1) < 2 ^ e.R := pre_lt e.h_fits hi (show e.R ≤ e.l (i + 1) by omega)
    have hne : e.c.type ≠ CODES := by
      intro ht
      have := (e.h_codes ht).2.1
      have h3 : e.mx = mxl e.f e.n := rfl
      omega
    by_cases hAi : e.l i ≤ e.R
    · -- no table so far: open one
      obtain ⟨hd0, hlow, hcR, huR⟩ := hphA hAi
      have hc : (decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true := by
        rw [cond_iff]
        refine ⟨by omega, ?_⟩
        rw [hlow, hmk]
        have := rev_lt e.R (e.p (i + 1))
        have h15 : 2 ^ e.R ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        have : (0xffffffff : UInt32).toNat = 4294967295 := rfl
        omega
      rw [ite_eq_left hc, ite_eq_left (by simp [hd0])]
      refine openBody_wp_budget e budget i _ ca ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, hroot,
        align_succ e.h_fits hi hRl (Or.inl hAi)⟩ ⟨hx.1.1, hx.2⟩
        ((startsAt_iff e.f e.n e.R hi).mpr ⟨hRl, Or.inl hAi⟩)
    · have hBi : e.R < e.l i := by omega
      obtain ⟨hd, hlow, hbb1, hbb2, hblk⟩ := hphB hBi
      by_cases hpe : e.p (i + 1) = e.p i
      · -- same prefix: the table stays
        have hc : ¬ ((decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true) := by
          rw [cond_iff]
          rintro ⟨_, hh⟩
          apply hh
          rw [hlow, hmk, hpe]
        rw [ite_eq_right hc]
        have hns : ¬ Canon.startsAt e.ls e.R i := fun h =>
          ((startsAt_iff e.f e.n e.R hi).mp h).2.elim (fun h' => by have h'' : e.l i ≤ e.R := h'; omega) (fun h' => h' hpe)
        refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inl ⟨hex, ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ?_⟩,
          ex_nostart e i s ca hns hx⟩, by rw [hex]; decide⟩
        refine ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, fun h => by omega, fun _ => ⟨hd, ?_, ?_, hbb2, ?_⟩⟩
        · rw [hlow, hpe]
        · exact hblk (i + 1) hi hRl hpe
        · intro j hj hRj hpj
          exact hblk j hj hRj (hpj.trans hpe)
      · -- new prefix
        have hc : (decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true := by
          rw [cond_iff]
          refine ⟨by omega, ?_⟩
          rw [hlow, hmk]
          intro heq
          apply hpe
          have := rev_inj e.R _ _ heq
          have hpi : e.p i < 2 ^ e.R := pre_lt e.h_fits (show i < Tc e.f e.n 15 by have : i + 1 < e.m := hi; unfold Env.m at this; omega) (show e.R ≤ e.l i by omega)
          rw [Nat.mod_eq_of_lt hpl, Nat.mod_eq_of_lt hpi] at this
          exact this
        have hdne : ¬ ((s.drop == 0) = true) := by
          simp only [beq_iff_eq]; intro h0; rw [h0] at hd; simp at hd; omega
        rw [ite_eq_left hc, ite_eq_right hdne]
        exact openBody_wp_budget e budget i _ ca ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hmin, hRl, hd,
          align_succ e.h_fits hi hRl (Or.inr ⟨hBi, hpe⟩)⟩ ⟨hx.1.1, hx.2⟩
          ((startsAt_iff e.f e.n e.R hi).mpr ⟨hRl, Or.inr hpe⟩)
  · -- the code is not longer than the root: no table
    have hc : ¬ ((decide (s.len > e.c.root) && s.huff &&& s.mask != s.low) = true) := by
      rw [cond_iff]; rintro ⟨h1, _⟩; omega
    rw [ite_eq_right hc]
    have hAi : e.l i ≤ e.R := by omega
    obtain ⟨hd0, hlow, hcR, huR⟩ := hphA hAi
    have hns : ¬ Canon.startsAt e.ls e.R i := fun h => by
      have : e.R < e.l (i + 1) := ((startsAt_iff e.f e.n e.R hi).mp h).1
      omega
    refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inl ⟨hex, ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, ?_⟩,
      ex_nostart e i s ca hns hx⟩, by rw [hex]; decide⟩
    refine ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, fun _ => ⟨hd0, hlow, hcR, huR⟩, fun h => by omega⟩


theorem jp1_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap) (i : Nat) (s : TS) (ca : Array Code) (h : MI1 e i s ca) (hx : Ex1 e i s ca)
    (hinc : i + 1 = e.m → s.huff.toNat ≠ 0 → Einc e s) :
    Wp (jp1 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPostX e i s' ca' ∧ s'.exit ≠ 2) := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hhfin, hmask, hcnt, hsz, hTab, hmin⟩ := h
  have hmono := fun (hi1 : i + 1 < e.m) => lenAt_mono (f := e.f) (n := e.n) (Nat.le_succ i) hi1
  have hi0 : i < Tc e.f e.n 15 := hi
  obtain ⟨hb1, hb2⟩ := lenAt_bounds (f := e.f) (n := e.n) hi0
  have hblk := (lenAt_eq_iff (f := e.f) (n := e.n) (l := lenAt e.f e.n i) hb1 hb2 hi0).mp rfl
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hTs := Tc_succ' (f := e.f) (n := e.n) hb1
  simp only [Env.l] at hlen hblk hTs
  have hlen16 : s.len.toNat < 16 := by rw [hlen]; exact Nat.lt_succ_of_le hb2
  have hsz16 : s.len.toNat < s.count.size := by rw [hcnt.1]; exact hlen16
  have hcl : (s.count[s.len.toNat]).toNat = Tc e.f e.n (lenAt e.f e.n i) - i := by
    have key := hcnt.2 (lenAt e.f e.n i) hb1 hb2
    rw [Array.getD_eq_getD_getElem?, show lenAt e.f e.n i = s.len.toNat from hlen.symm, Array.getElem?_eq_getElem hsz16] at key
    simp only [Option.getD_some] at key
    rw [key, hlen]; unfold rem; omega
  have hcl_pos : 1 ≤ (s.count[s.len.toNat]).toNat := by rw [hcl]; omega
  have hcl1 : ((s.count[s.len.toNat]) - 1).toNat = (s.count[s.len.toNat]).toNat - 1 := by
    rw [UInt16.toNat_sub_of_le _ _ (by simp [UInt16.le_iff_toNat_le]; omega)]; rfl
  have hcnt' : ∀ cnt' : Array UInt16, cnt' = s.count.set! s.len.toNat ((s.count[s.len.toNat]) - 1) →
      CountOK e cnt' (i + 1) := by
    intro cnt' hc'
    refine ⟨by rw [hc', Array.size_set!]; exact hcnt.1, fun l hl1 hl2 => ?_⟩
    rw [hc', getD_set!, rem_succ hl1 hl2 hi0]
    by_cases hl : s.len.toNat = l
    · have hli : lenAt e.f e.n i = l := by rw [← hl]; exact hlen.symm
      rw [ite_eq_left ⟨hl, hsz16⟩, ite_eq_left hli, hcl1, hcl]
      subst hli
      unfold rem; omega
    · have hli : ¬ (lenAt e.f e.n i = l) := by intro h2; apply hl; rw [hlen]; exact h2
      rw [ite_eq_right (fun h2 => hl h2.1), ite_eq_right hli, Nat.sub_zero]
      exact hcnt.2 l hl1 hl2
  unfold jp1
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  have hsym' : (sym + 1).toNat = i + 1 := by
    have := e.h_n; have : e.m ≤ e.n := Tc_le 15 e.n
    rw [u32_succ (by omega), hsym]
  apply Wp.bind' (Q := fun r h' => r = count[len.toNat] ∧ h' = e.hc ca) (Wp.pure_eq (geta_eq hsz16) ⟨rfl, rfl⟩)
  rintro cl h' ⟨rfl, rfl⟩
  try dsimp only
  apply Wp.bind' (Q := fun r h' => r = count.set! len.toNat (count[len.toNat] - 1) ∧ h' = e.hc ca)
    (Wp.pure_eq (seta_eq hsz16) ⟨rfl, rfl⟩)
  rintro cnt' h' ⟨hc', rfl⟩
  try dsimp only
  have hCO := hcnt' cnt' hc'
  have tail : ∀ (s2 : TS), s2.exit = 0 → s2.sym.toNat = i + 1 → s2.len.toNat = e.l (i + 1) → i + 1 < e.m →
      s2.huff = huff → s2.mask = mask → s2.count = cnt' → s2.curr = curr → s2.drop = drop → s2.low = low →
      s2.used = used → s2.min = min → s2.next = next →
      Wp (jp2 e.c s2) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPostX e i s' ca' ∧ s'.exit ≠ 2) := by
    intro s2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    have hx2 : Ex1 e i s2 ca := by
      refine ⟨?_, hx.2⟩
      have := hx.1
      unfold DescIs DescB at this ⊢
      rw [h13, h8, h11, h9, h10]; exact this
    refine Wp.mono (jp2_wp_budget e budget i s2 ca ?_ hx2) ?_
    · refine ⟨h4, h1, h2, h3, ?_, by rw [h6]; exact hmask, by rw [h7]; exact hCO, hsz, ?_, by rw [h12, h8]; exact hmin⟩
      · rw [h5]; exact hhuff h4
      · obtain ⟨⟨k, hn, hk⟩, r⟩ := hTab
        unfold TabSt
        rw [h13, h8, h11, h9, h10]
        exact ⟨⟨k, hn, hk⟩, r⟩
    · rintro s' h' ⟨ca', hh, hf, hr, noRefusal⟩
      refine ⟨ca', hh, hf, ?_, noRefusal⟩
      rcases hr with ⟨hx', hm, hEx⟩ | ⟨hx', hy, hz⟩
      · exact ⟨Or.inl ⟨h4, hm⟩, fun _ _ => hEx, fun h => absurd h (by omega)⟩
      · exact ⟨Or.inr (Or.inr ⟨hx', hy, hz⟩), fun _ h => by rw [hx'] at h; exact absurd h (by decide),
          fun _ h => by rw [hx'] at h; exact absurd h (by decide)⟩
  have hmxeq : (len == e.c.max) = true ↔ lenAt e.f e.n i = e.mx := by
    rw [beq_iff_eq, ← UInt32.toNat_inj, e.h_max, hlen]; rfl
  have hTle : e.m ≤ e.n := Tc_le 15 e.n
  by_cases hz : ((count[len.toNat] - 1 == 0) = true)
  · rw [ite_eq_left hz]
    have hcl0 : (count[len.toNat] - 1).toNat = 0 := by
      have := beq_iff_eq.mp hz
      rw [this]; rfl
    have hTl : i + 1 = Tc e.f e.n (lenAt e.f e.n i) := by omega
    by_cases hmx : (len == e.c.max) = true
    · rw [ite_eq_left hmx]
      have hlm := hmxeq.mp hmx
      have him : i + 1 = e.m := by
        have h1 : Tc e.f e.n e.mx = Tc e.f e.n 15 := by
          have := Tc_mono (f := e.f) (n := e.n) (show e.mx ≤ 15 from hmxle)
          have hh := (lenAt_le_iff (f := e.f) (n := e.n) (l := e.mx) hmxle (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)).mp (Nat.le_refl _)
          omega
        rw [hTl, hlm]; exact h1
      refine Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, ⟨Or.inr (Or.inl ⟨him, rfl, ?_, hsz⟩),
        fun h _ => absurd h (by omega), fun _ _ => ⟨cont_final e i ca him hx.2, fun hne => hinc him hne⟩⟩, by change (1 : UInt8) ≠ 2; decide⟩
      obtain ⟨⟨k, hn, hk⟩, hu, _⟩ := hTab
      exact ⟨⟨k, hn, hk⟩, hu, hhfin him⟩
    · rw [ite_eq_right hmx]
      have hi1 : i + 1 < e.m := by
        apply Classical.byContradiction
        intro hcon
        apply hmx
        rw [hmxeq]
        have him : i + 1 = e.m := by omega
        have : i = Tc e.f e.n 15 - 1 := by have : e.m = Tc e.f e.n 15 := rfl; omega
        rw [this]; rfl
      have hwlt : e.ow + (i + 1) < e.wa.size := by have := e.h_wa; omega
      have hw := e.h_wcont (i + 1) hi1
      rw [Array.getElem?_eq_getElem hwlt] at hw
      have hw' : e.wa[e.ow + (i + 1)]'hwlt = UInt16.ofNat ((wsAux e.f e.n 15).getD (i + 1) 0) := Option.some.inj hw
      have hwsm : (wsAux e.f e.n 15).getD (i + 1) 0 < e.n := ws_getD_lt (by omega)
      have hlenx : e.l (i + 1) = e.f ((wsAux e.f e.n 15).getD (i + 1) 0) := rfl
      generalize (wsAux e.f e.n 15).getD (i + 1) 0 = x at hw' hwsm hlenx
      have hn288 := e.h_n
      have hx16 : x < 2 ^ 16 := by omega
      have hwn : (UInt16.ofNat x).toNat = x := by
        rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hx16]
      rw [e.h_work, e.h_lens]
      apply Wp.bind' (Q := fun r h' => r = e.wa[e.ow + (i + 1)]'hwlt ∧ h' = e.hc ca)
      · rw [hsym']; exact Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩
      · rintro w h' ⟨rfl, rfl⟩
        rw [hw']
        have hlr : e.ol + (UInt16.ofNat x).toNat < e.la.size := by
          rw [hwn]; have := e.h_la; omega
        apply Wp.bind' (Q := fun r h' => r = e.la[e.ol + (UInt16.ofNat x).toNat]'hlr ∧ h' = e.hc ca)
        · exact Wp.of_eq (Ptr.index_ok (e.get_la ca) hlr) ⟨rfl, rfl⟩
        · rintro l h' ⟨rfl, rfl⟩
          have hlv : (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toNat = e.l (i + 1) := by
            have hf := e.h_f x
            rw [hlenx, hf, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show e.ol + x < e.la.size by rw [hwn] at hlr; exact hlr),
              Option.getD_some]
            simp only [hwn]
          have hl32 : (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toUInt32.toNat = e.l (i + 1) := by
            rw [UInt16.toNat_toUInt32]; exact hlv
          exact tail { huff := huff, sym := sym + 1, len := (e.la[e.ol + (UInt16.ofNat x).toNat]'hlr).toUInt32, curr := curr, drop := drop, low := low, used := used, min := min, fill := fill, incr := incr, mask := mask, left := left, next := next, here := here, count := cnt', exit := exit } hex hsym' hl32 hi1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · rw [ite_eq_right hz]
    have hcl2 : 2 ≤ (count[len.toNat]).toNat := by
      apply Classical.byContradiction
      intro hcon
      apply hz
      have : (count[len.toNat]).toNat = 1 := by omega
      have h1 : count[len.toNat] = 1 := by
        apply UInt16.toNat_inj.mp; rw [this]; rfl
      rw [h1]; rfl
    have hi1 : i + 1 < Tc e.f e.n (lenAt e.f e.n i) := by omega
    have hmi1 : i + 1 < e.m := by
      have := Tc_mono (f := e.f) (n := e.n) hb2
      have : e.m = Tc e.f e.n 15 := rfl
      omega
    have hl' : e.l (i + 1) = lenAt e.f e.n i := by
      have := (lenAt_eq_iff (f := e.f) (n := e.n) (l := lenAt e.f e.n i) hb1 hb2 hmi1).mpr ⟨by omega, hi1⟩
      exact this
    exact tail { huff := huff, sym := sym + 1, len := len, curr := curr, drop := drop, low := low, used := used, min := min, fill := fill, incr := incr, mask := mask, left := left, next := next, here := here, count := cnt', exit := exit } hex hsym' (by rw [hl']; exact hlen) hmi1 rfl rfl rfl rfl rfl rfl rfl rfl rfl


theorem jp0_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap) (i : Nat) (s : TS) (ca : Array Code) (h : MI e i s ca) (hEx : Ex e i s ca)
    (hhere0 : s.here = e.here i) :
    Wp (jp0 e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPostX e i s' ca' ∧ s'.exit ≠ 2) := by
  obtain ⟨hi, hex, hsym, hlen, hhuff, hmask, hcnt, hsz, hTab⟩ := h
  have hTab' := hTab
  obtain ⟨⟨k, hnext, hku⟩, hucap, hu2R, hc1, hc15, hphA, hphB⟩ := hTab'
  have hi0 : i < Tc e.f e.n 15 := hi
  have hbd : 1 ≤ e.l i ∧ e.l i ≤ 15 := lenAt_bounds (f := e.f) (n := e.n) hi0
  have hR1 := e.h_R1
  have hdb : s.drop.toNat ≤ s.len.toNat ∧ s.len.toNat - s.drop.toNat ≤ s.curr.toNat ∧
      1 ≤ s.len.toNat - s.drop.toNat ∧ s.drop.toNat ≤ 15 := by
    by_cases hA : e.l i ≤ e.R
    · obtain ⟨hd0, _, hcR, _⟩ := hphA hA
      rw [hd0]
      simp only [UInt32.toNat_zero]
      omega
    · obtain ⟨hd, _, hbb1, hbb2, _⟩ := hphB (by omega)
      omega
  obtain ⟨hdn, hbc1, hbc2, hbc3⟩ := hdb
  have hb32 : (s.len - s.drop).toNat < 32 := by rw [u32_sub hdn]; omega
  have hcurr32 : s.curr.toNat < 32 := by omega
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by have := e.h_pos; unfold Env.m; omega)
    exact this.2
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  rcases s with ⟨huff, sym, len, curr, drop, low, used, min, fill, incr, mask, left, next, here, count, exit⟩
  dsimp only at *
  obtain ⟨hdesc, hcont⟩ := hEx
  obtain ⟨⟨⟨k', hk'1, hk'2⟩, hcurrD, husedD⟩, hdropD, hlowD⟩ := hdesc
  have hkb : k = (e.D i).base := by
    have := Ptr.ref.inj (hnext.symm.trans hk'1)
    have : k = k' := by omega
    rw [this]; exact hk'2
  unfold jp0
  apply Wp.bind' (Q := fun r h' => r = 1 <<< (len - drop) ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hb32) ⟨rfl, rfl⟩)
  rintro incr0 h' ⟨rfl, rfl⟩
  apply Wp.bind' (Q := fun r h' => r = 1 <<< curr ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hcurr32) ⟨rfl, rfl⟩)
  rintro fill0 h' ⟨rfl, rfl⟩
  have hS : ((1 : UInt32) <<< (len - drop)).toNat = 2 ^ (len.toNat - drop.toNat) := by rw [u32_shl1 hb32, u32_sub hdn]
  have hF : ((1 : UInt32) <<< curr).toNat = 2 ^ curr.toNat := u32_shl1 hcurr32
  have hSN : 2 ^ (len.toNat - drop.toNat) * 2 ^ (curr.toNat - (len.toNat - drop.toNat)) = 2 ^ curr.toNat := by
    rw [← Nat.pow_add]; congr 1; omega
  have hhd : (huff >>> drop).toNat = huff.toNat / 2 ^ drop.toNat := u32_shr (by omega)
  have hhdS : huff.toNat / 2 ^ drop.toNat < 2 ^ (len.toNat - drop.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← Nat.pow_add, show len.toNat - drop.toNat + drop.toNat = len.toNat by omega,
      hhuff, hlen]
    exact rev_lt _ _
  dsimp only
  have hN1 : 1 ≤ 2 ^ (curr.toNat - (len.toNat - drop.toNat)) := Nat.pow_pos (by omega)
  have hS1 : 1 ≤ 2 ^ (len.toNat - drop.toNat) := Nat.pow_pos (by omega)
  apply Wp.bind' (fill_loop e _ ca (2 ^ (len.toNat - drop.toNat)) (2 ^ (curr.toNat - (len.toNat - drop.toNat))) k
    (huff.toNat / 2 ^ drop.toNat) hnext hS (by rw [hF, hSN]) hN1 hS1 hhd hhdS (show drop.toNat < 32 by omega)
    (by rw [hSN]; omega) hsz)
  rintro s2 h' ⟨ca2, rfl, rfl, hs2, hp1, hp2⟩
  dsimp only
  have hfr : FrameCA e ca ca2 := by
    refine ⟨hs2, fun x hx => hp2 x ?_⟩
    rintro ⟨q', hq', hxq⟩
    have h1 : 2 ^ (len.toNat - drop.toNat) * (q' + 1) ≤ 2 ^ (len.toNat - drop.toNat) * 2 ^ (curr.toNat - (len.toNat - drop.toNat)) :=
      Nat.mul_le_mul_left _ hq'
    rw [Nat.mul_succ] at h1
    rw [hSN] at h1
    omega
  have hl31 : (len - 1).toNat < 32 := by rw [u32_one_sub (by omega)]; omega
  apply Wp.bind' (Q := fun r h' => r = 1 <<< (len - 1) ∧ h' = e.hc ca2) (Wp.pure_eq (shl32_eq hl31) ⟨rfl, rfl⟩)
  rintro incr2 h' ⟨rfl, rfl⟩
  apply Wp.bind' (incr_loop _ (len.toNat - 1) (by omega)
    (by rw [u32_shl1 hl31, u32_one_sub (by omega)]) (e.hc ca2))
  rintro s4 h' ⟨rfl, X, rfl, hX⟩
  dsimp only at hX ⊢
  have hlen1 : len.toNat - 1 = e.l i - 1 := by omega
  rw [hlen1] at hX
  have hXr : X.toNat = incrLoop (rev (e.l i) (e.v i)) (e.l i - 1) := by rw [hX, hhuff]
  -- the continuation, once the new `huff` is known
  have mi1 : ∀ hnew : UInt32, (i + 1 < e.m → hnew.toNat = rev (e.l (i + 1)) (e.v (i + 1))) →
      (i + 1 = e.m → hnew.toNat = 0 ∨ hnew.toNat < 2 ^ curr.toNat) →
      (i + 1 = e.m → hnew.toNat ≠ 0 → Einc e (TS.mk hnew sym len curr drop low used (1 <<< curr) 0 X mask left next here count exit)) →
      Wp (jp1 e.c (TS.mk hnew sym len curr drop low used (1 <<< curr) 0 X mask left next here count exit)) (e.hc ca2)
        (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPostX e i s' ca' ∧ s'.exit ≠ 2) := by
    intro hnew hA hB hC
    refine Wp.mono (jp1_wp_budget e budget i _ ca2 ?_ ?_ hC) ?_
    · refine ⟨hi, hex, hsym, hlen, hA, hB, hmask, hcnt, by omega, hTab, ?_⟩
      show ((1 : UInt32) <<< curr).toNat = 2 ^ curr.toNat
      exact hF
    · refine ⟨⟨⟨⟨k', hk'1, hk'2⟩, hcurrD, husedD⟩, hdropD, hlowD⟩, ?_⟩
      have hLd : len.toNat = Canon.L e.ls i := by rw [hlen]; exact (L_eq e.f e.n hi).symm
      have hHd : huff.toNat = Canon.H e.ls i := by rw [hhuff]; exact (H_eq e.f e.n hi).symm
      refine cont_fill e i ca ca2 hi k (huff.toNat / 2 ^ drop.toNat) (2 ^ (len.toNat - drop.toNat))
        (2 ^ (curr.toNat - (len.toNat - drop.toNat))) hkb (by rw [hHd, hdropD]) (by rw [hLd, hdropD])
        (by unfold gReps; rw [hLd, hdropD, hcurrD]; rfl) ?_ ?_ hcont
      · intro x hx
        rw [← hhere0]; exact hp1 x hx
      · intro x hx
        exact hp2 x hx
    · rintro s' h' ⟨ca', hh, hf, hr, noRefusal⟩
      exact ⟨ca', hh, hfr.trans hf, hr, noRefusal⟩
  have hi1 := e.h_fits
  by_cases hXz : X = 0
  · have hXz' : (X != 0) = false := by simp [hXz]
    rw [ite_eq_right (by simp [hXz])]
    refine mi1 0 (fun hlt => ?_) (fun _ => Or.inl rfl) (fun _ h => absurd rfl h)
    exfalso
    obtain ⟨e', _, hinc, _⟩ := huff_step (f := e.f) (n := e.n) hi1 hlt
    have : X.toNat = 0 := by rw [hXz]; rfl
    have h3 : X.toNat = 2 ^ e' := hXr.trans hinc
    rw [this] at h3
    exact absurd h3.symm (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega)))
  · rw [ite_eq_left (by simpa using hXz)]
    have hXn : X.toNat ≠ 0 := fun h0 => hXz (UInt32.toNat_inj.mp (by rw [h0]; rfl))
    obtain ⟨e', he', hXp⟩ : ∃ e', e' ≤ e.l i - 1 ∧ X.toNat = 2 ^ e' := by
      rcases incrLoop_pow huff.toNat (e.l i - 1) with h0 | ⟨e', he', h1⟩
      · exact absurd (hX.trans h0) hXn
      · exact ⟨e', he', hX.trans h1⟩
    have hX1 : (X - 1).toNat = 2 ^ e' - 1 := by rw [u32_one_sub hXn, hXp]
    have hand : (huff &&& (X - 1)).toNat = huff.toNat % 2 ^ e' := u32_and_mod hX1
    have hmodlt : huff.toNat % 2 ^ e' < 2 ^ e' := Nat.mod_lt _ (Nat.pow_pos (by omega))
    have hp15 : 2 ^ e' ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have hnewv : ((huff &&& (X - 1)) + X).toNat = huff.toNat % 2 ^ e' + 2 ^ e' := by
      have hlt : (huff &&& (X - 1)).toNat + X.toNat < 2 ^ 32 := by rw [hand, hXp]; omega
      rw [u32_add hlt, hand, hXp]
    have hincl : i + 1 = e.m → e.m = 1 ∧ e.R = 1 ∧ e.l i = 1 ∧ k = 0 ∧ e' = 0 := by
      intro him
      have hnc : ¬ (Kc e.f e.n 15 = 2 ^ 15) := by
        intro hc
        have := huff_last (f := e.f) (n := e.n) hc (m := i) (by have : e.m = Tc e.f e.n 15 := rfl; omega)
        have h0 : X.toNat = 0 := by rw [hXr]; exact this
        exact hXn h0
      have hmx1 : mxl e.f e.n = 1 := by
        rcases e.h_end with h | h
        · exact absurd h hnc
        · exact h.1
      have hT1 : Tc e.f e.n 15 = 1 := by
        rcases e.h_end with h | h
        · exact absurd h hnc
        · exact h.2.1
      have hlm : e.l i ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i ≤ Tc e.f e.n 15 - 1 by omega) (by have := e.h_pos; omega)
      have hl1 : e.l i = 1 := by have : e.mx = mxl e.f e.n := rfl; omega
      have hAi : e.l i ≤ e.R := by omega
      obtain ⟨_, _, hcR, huR⟩ := hphA hAi
      have hRR : e.R = 1 := by have := e.h_Rmx; omega
      have hk0 : k = 0 := by
        have : 2 ^ curr.toNat = 2 ^ e.R := by rw [hcR]
        omega
      exact ⟨hT1, hRR, hl1, hk0, by omega⟩
    refine mi1 _ (fun hlt => ?_) (fun him => ?_) (fun him hne => ?_)
    · obtain ⟨e2, _, hinc, hrev⟩ := huff_step (f := e.f) (n := e.n) hi1 hlt
      have : 2 ^ e' = 2 ^ e2 := by
        rw [← hXp, hXr]
        exact hinc
      rw [hnewv, this, hhuff]
      exact hrev
    · right
      -- the code is incomplete: its only symbol has length 1
      have hnc : ¬ (Kc e.f e.n 15 = 2 ^ 15) := by
        intro hc
        have := huff_last (f := e.f) (n := e.n) hc (m := i) (by have : e.m = Tc e.f e.n 15 := rfl; omega)
        have h0 : X.toNat = 0 := by rw [hXr]; exact this
        exact hXn h0
      have hmx1 : mxl e.f e.n = 1 := by
        rcases e.h_end with h | h
        · exact absurd h hnc
        · exact h.1
      have hlm : e.l i ≤ e.mx := lenAt_mono (f := e.f) (n := e.n) (show i ≤ Tc e.f e.n 15 - 1 by omega) (by have := e.h_pos; omega)
      have hl1 : e.l i = 1 := by have : e.mx = mxl e.f e.n := rfl; omega
      have hAi : e.l i ≤ e.R := by omega
      obtain ⟨_, _, hcR, _⟩ := hphA hAi
      rw [hnewv]
      have h2 : e' = 0 := by omega
      subst h2
      have := Nat.mod_lt huff.toNat (Nat.pow_pos (a := 2) (n := 0) (by omega))
      have hcpos : 2 ^ 1 ≤ 2 ^ curr.toNat := Nat.pow_le_pow_right (by omega) (by omega)
      simp at this
      omega
    · obtain ⟨hm1, hRR, hl1, hk0, he0⟩ := hincl him
      refine ⟨hm1, hRR, ?_, ?_⟩
      · show ((huff &&& (X - 1)) + X).toNat = 1
        rw [hnewv, he0]; simp [Nat.pow_zero, Nat.mod_one]
      · show next = .ref e.rc e.oc
        rw [hnext, hk0]; rfl


theorem hereTop_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap) (i : Nat) (s : TS) (ca : Array Code) (h : MI e i s ca) (hEx : Ex e i s ca) :
    Wp (hereTop e.c s) (e.hc ca) (fun s' h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ StepPostX e i s' ca' ∧ s'.exit ≠ 2) := by
  have hMI := h
  have hsym : s.sym.toNat = i := h.2.2.1
  have hi : i < e.m := h.1
  have hn288 := e.h_n
  have hTle : e.m ≤ e.n := Tc_le 15 e.n
  have hwlt : e.ow + i < e.wa.size := by have := e.h_wa; omega
  have hw := e.h_wcont i hi
  rw [Array.getElem?_eq_getElem hwlt] at hw
  have hw' : e.wa[e.ow + i]'hwlt = UInt16.ofNat ((wsAux e.f e.n 15).getD i 0) := Option.some.inj hw
  have hx : (wsAux e.f e.n 15).getD i 0 < e.n := ws_getD_lt hi
  generalize hxd : (wsAux e.f e.n 15).getD i 0 = x at hw' hx
  have hbits : (s.len - s.drop).toUInt8 = (Canon.L e.ls i - (e.D i).drop).toUInt8 := by
    rw [u32_toUInt8]
    have hdr := hEx.1.2.1
    have hle : s.drop.toNat ≤ s.len.toNat := by
      obtain ⟨_, _, _, hlen', _, _, _, _, hTab⟩ := h
      obtain ⟨_, _, _, _, _, hA, hB⟩ := hTab
      by_cases hh : e.l i ≤ e.R
      · rw [(hA hh).1]; simp
      · have := (hB (by omega)).1; omega
    rw [u32_sub hle, hdr, h.2.2.2.1]
    exact congrArg (fun t => (t - (e.D i).drop).toUInt8) (L_eq e.f e.n hi).symm
  have hhereE : e.here i = hereC e.c (UInt16.ofNat x) (s.len - s.drop).toUInt8 := by
    unfold Env.here; rw [hxd, hbits]
  have hx16 : x < 2 ^ 16 := by omega
  have hwn : (UInt16.ofNat x).toNat = x := by rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hx16]
  have hw32 : (UInt16.ofNat x).toUInt32.toNat = x := by rw [UInt16.toNat_toUInt32, hwn]
  -- the table lookups are in range
  have hidx : x ≥ e.c.match_.toNat →
      x - e.c.match_.toNat < e.c.extra.size ∧ x - e.c.match_.toNat < e.c.base.size := by
    intro hge
    rcases e.h_type with ht | ht | ht
    · obtain ⟨_, _, h3, h4⟩ := e.h_codes ht
      have hm : e.c.match_.toNat = 20 := by rw [h4]; rfl
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := e.h_lens' ht
      have hm : e.c.match_.toNat = 257 := by rw [h4]; rfl
      have hl1 : lbase.size = 31 := rfl
      have hl2 : lext.size = 31 := rfl
      rw [h2, h3, hm] at *
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := e.h_dists ht
      have hm : e.c.match_.toNat = 0 := by rw [h4]; rfl
      have hl1 : dbase.size = 32 := rfl
      have hl2 : dext.size = 32 := rfl
      rw [h2, h3, hm] at *
      omega
  unfold hereTop
  dsimp only
  rw [e.h_work]
  rw [hsym]
  apply Wp.bind' (Q := fun r h' => r = e.wa[e.ow + i]'hwlt ∧ h' = e.hc ca)
    (Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩)
  rintro w h' ⟨rfl, rfl⟩
  rw [hw']
  have rd : Wp (Ptr.index (Ptr.ref e.rw e.ow) (i : Int)) (e.hc ca) (fun r h' => r = e.wa[e.ow + i]'hwlt ∧ h' = e.hc ca) :=
    Wp.of_eq (Ptr.index_ok (e.get_wa ca) hwlt) ⟨rfl, rfl⟩
  by_cases h1 : (UInt16.ofNat x).toUInt32 + 1 < e.c.match_
  · rw [ite_eq_left h1]
    try dsimp only
    apply Wp.bind' rd
    rintro w2 h' ⟨rfl, rfl⟩
    rw [hw']
    refine jp0_wp_budget e budget i _ ca hMI hEx ?_
    show _ = e.here i
    rw [hhereE]; unfold hereC; rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    try dsimp only
    apply Wp.bind' rd
    rintro w2 h' ⟨rfl, rfl⟩
    rw [hw']
    by_cases h2 : (UInt16.ofNat x).toUInt32 ≥ e.c.match_
    · rw [ite_eq_left h2]
      have hge : x ≥ e.c.match_.toNat := by
        have := UInt32.le_iff_toNat_le.mp h2; rw [hw32] at this; exact this
      obtain ⟨hx1, hx2⟩ := hidx hge
      have hsb : ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = x - e.c.match_.toNat := by
        rw [u32_sub (by rw [hw32]; exact hge), hw32]
      apply Wp.bind' rd
      rintro w3 h' ⟨rfl, rfl⟩
      rw [hw']
      have ga : geta e.c.extra ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = pure (e.c.extra[x - e.c.match_.toNat]'hx1) := by
        rw [hsb]; exact geta_eq hx1
      have gb : geta e.c.base ((UInt16.ofNat x).toUInt32 - e.c.match_).toNat = pure (e.c.base[x - e.c.match_.toNat]'hx2) := by
        rw [hsb]; exact geta_eq hx2
      apply Wp.bind' (Q := fun r h' => r = e.c.extra[x - e.c.match_.toNat]'hx1 ∧ h' = e.hc ca)
        (Wp.pure_eq ga ⟨rfl, rfl⟩)
      rintro ex h' ⟨rfl, rfl⟩
      try dsimp only
      apply Wp.bind' rd
      rintro w4 h' ⟨rfl, rfl⟩
      rw [hw']
      apply Wp.bind' (Q := fun r h' => r = e.c.base[x - e.c.match_.toNat]'hx2 ∧ h' = e.hc ca)
        (Wp.pure_eq gb ⟨rfl, rfl⟩)
      rintro ba h' ⟨rfl, rfl⟩
      try dsimp only
      refine jp0_wp_budget e budget i _ ca hMI hEx ?_
      show _ = e.here i
      rw [hhereE]; unfold hereC; rw [ite_eq_right h1, ite_eq_left h2, hsb]
      simp [getElem!_pos, hx1, hx2]
    · rw [ite_eq_right h2]
      refine jp0_wp_budget e budget i _ ca hMI hEx ?_
      show _ = e.here i
      rw [hhereE]; unfold hereC; rw [ite_eq_right h1, ite_eq_right h2]

#print axioms openBody_wp_budget
#print axioms jp2_wp_budget
#print axioms jp1_wp_budget
#print axioms jp0_wp_budget
#print axioms hereTop_wp_budget

theorem itTail_cells_wp_budget (e : Env) (budget : ∀ j, j < e.m → (e.D j).used ≤ e.cap) (ca : Array Code) (count : Array UInt16) (bits min : UInt32) (left : Int32)
    (hcnt : CountOK e count 0) (hmin : min.toNat = e.l 0) (hsz : e.oc + e.cap ≤ ca.size) :
    Wp (itTail e.c.type e.c.lens e.c.table bits e.c.work count e.c.max min e.c.root left e.c.base e.c.extra
        e.c.match_) (e.hc ca)
      (fun r h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
        ((r.1 = 0 ∧ ∃ u, u ≤ e.cap ∧ r.2.1 = .ref e.rc (e.oc + u) ∧ r.2.2 = e.c.root) ∨
         (r.1 = 1 ∧ r.2.1 = e.c.table ∧ r.2.2 = bits)) ∧ (r.1 = 1 → e.c.type ≠ CODES) ∧
        (r.1 = 0 → Cont e e.m e.m ca') ∧ TailDetails e r ca' ∧ r.1 = 0) := by
  have hR1 := e.h_R1
  have hroot := e.h_root
  have hpos := e.h_pos
  have hmxle : e.mx ≤ 15 := by
    have := lenAt_bounds (f := e.f) (n := e.n) (show e.m - 1 < Tc e.f e.n 15 by unfold Env.m; omega)
    exact this.2
  have hRmx := e.h_Rmx
  have hm15 : e.m = Tc e.f e.n 15 := rfl
  have hmx15 : e.mx = mxl e.f e.n := rfl
  have hR32 : e.c.root.toNat < 32 := by omega
  unfold itTail
  apply Wp.bind' (Q := fun r h' => r = 1 <<< e.c.root ∧ h' = e.hc ca) (Wp.pure_eq (shl32_eq hR32) ⟨rfl, rfl⟩)
  rintro used0 h' ⟨rfl, rfl⟩
  have hu0 : ((1 : UInt32) <<< e.c.root).toNat = 2 ^ e.R := by rw [u32_shl1 hR32, hroot]
  have rootBudget : 2 ^ e.R ≤ e.cap := by
    have first := budget 0 e.h_pos
    exact first
  have initialGuard := tooBig_false_of_budget e (show ((1 : UInt32) <<< e.c.root).toNat ≤ e.cap by omega)
  by_cases hb : tooBig e.c.type (1 <<< e.c.root) = true
  · rw [initialGuard] at hb
    contradiction
  · rw [ite_eq_right hb]
    have hb' : tooBig e.c.type (1 <<< e.c.root) = false := by simpa using hb
    have hu0cap : 2 ^ e.R ≤ e.cap := by
      by_cases hc : e.c.type = CODES
      · obtain ⟨h1, h2, _, _⟩ := e.h_codes hc
        have hcap := e.h_cap
        rw [ite_eq_left hc] at hcap
        have : 2 ^ e.R ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · have := tooBig_le e hb' hc
        omega
    have hMI0 : MI e 0 (TS.mk 0 0 min e.c.root 0 0xffffffff (1 <<< e.c.root) min 0 0 ((1 <<< e.c.root) - 1) left
        e.c.table default count 0) ca := by
      refine ⟨hpos, rfl, rfl, hmin, ?_, ?_, hcnt, hsz, ?_⟩
      · show (0 : UInt32).toNat = rev (e.l 0) (e.v 0)
        rw [show e.v 0 = 0 from val_zero hpos, rev_zero]; rfl
      · show ((1 <<< e.c.root) - 1 : UInt32).toNat = 2 ^ e.R - 1
        rw [u32_sub (by rw [hu0]; exact Nat.pow_pos (by omega)), hu0]
        simp [UInt32.toNat_one]
      · refine ⟨⟨0, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun _ => ⟨rfl, rfl, ?_, ?_⟩, fun h => ?_⟩
        · show e.c.table = .ref e.rc (e.oc + 0); rw [e.h_table]; rfl
        · show 0 + 2 ^ e.c.root.toNat = ((1 : UInt32) <<< e.c.root).toNat; rw [hu0, hroot]; omega
        · show ((1 : UInt32) <<< e.c.root).toNat ≤ e.cap; omega
        · show 2 ^ e.R ≤ ((1 : UInt32) <<< e.c.root).toNat; omega
        · show 1 ≤ e.c.root.toNat; omega
        · show e.c.root.toNat ≤ 15; omega
        · show e.c.root.toNat = e.R; omega
        · show ((1 : UInt32) <<< e.c.root).toNat = 2 ^ e.R; omega
        · have := e.h_R0; have : e.l 0 = lenAt e.f e.n 0 := rfl; omega
    have hEx0 : Ex e 0 (TS.mk 0 0 min e.c.root 0 0xffffffff (1 <<< e.c.root) min 0 0 ((1 <<< e.c.root) - 1) left
        e.c.table default count 0) ca := by
      have hD0 : e.D 0 = ⟨0, e.R, 0, 2 ^ e.R, 2 ^ 32 - 1⟩ := rfl
      refine ⟨?_, fun _ => ⟨fun j hj => absurd hj (by omega), fun a h1 h2 => by omega⟩⟩
      unfold DescIs DescB
      rw [hD0]
      refine ⟨⟨⟨0, ?_, rfl⟩, ?_, ?_⟩, rfl, ?_⟩
      · show e.c.table = .ref e.rc (e.oc + 0); rw [e.h_table]; rfl
      · show e.c.root.toNat = e.R; omega
      · show ((1 : UInt32) <<< e.c.root).toNat = 2 ^ e.R; omega
      · show (0xffffffff : UInt32).toNat = 2 ^ 32 - 1; rfl
    have hTle : e.m ≤ e.n := Tc_le 15 e.n
    have hn288 := e.h_n
    apply Wp.bind' (Q := fun s h' => (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 1 ∧ Final e s ∧
          e.oc + e.cap ≤ ca'.size ∧ Cont e e.m e.m ca' ∧ (s.huff.toNat ≠ 0 → Einc e s) ∧ EndFields e s) ∨
        False)
      (Wp.cwhile
        (fun (s : TS) h' => (∃ i ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ MI e i s ca' ∧ Ex e i s ca') ∨
          (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 1 ∧ Final e s ∧ e.oc + e.cap ≤ ca'.size ∧
            Cont e e.m e.m ca' ∧ (s.huff.toNat ≠ 0 → Einc e s) ∧ EndFields e s) ∨
          False)
        (fun (s : TS) => if s.exit = 0 then e.m + 1 - s.sym.toNat else 0) _ ?_ (Or.inl ⟨0, ca, rfl, ⟨rfl, fun _ _ => rfl⟩, hMI0, hEx0⟩) ?_)
    · rintro s h' hinv
      rcases hinv with ⟨ca', rfl, hf, hx, hfin, hsz', hcF, hinc, endFields⟩ | impossible
      · rw [ite_eq_right (by simp [hx])]
        obtain ⟨⟨k, hn, hk⟩, hucap, hh⟩ := hfin
        by_cases hh0 : s.huff = 0
        · rw [ite_eq_right (by simp [hh0])]
          show Wp (do let table ← Ptr.add e.c.table ↑s.used.toNat; pure (0, table, e.c.root)) _ _
          rw [e.h_table]
          apply Wp.bind' (wp_add e ca' e.oc s.used.toNat (by omega))
          rintro q h' ⟨rfl, rfl⟩
          refine Wp.pure' ⟨ca', rfl, hf, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide), fun _ => hcF, ?_, rfl⟩
          intro _
          refine ⟨s.used.toNat, rfl, endFields.1.2.2, ?_⟩
          intro single one
          have impossible := endFields.2.2.2 single one
          rw [hh0] at impossible
          contradiction
        · rw [ite_eq_left (by simpa using hh0)]
          have hhlt : s.huff.toNat < 2 ^ s.curr.toNat := by
            rcases hh with h0 | h0
            · exact absurd (UInt32.toNat_inj.mp (by rw [h0]; rfl)) hh0
            · exact h0
          have hidx : e.oc + k + s.huff.toNat < ca'.size := by
            have := hf.1; omega
          show Wp (do let __r ← storeCode s.next s.huff.toNat ⟨64, (s.len - s.drop).toUInt8, 0⟩
                      let table ← Ptr.add e.c.table ↑s.used.toNat; pure (0, table, e.c.root)) _ _
          unfold storeCode
          rw [hn, e.h_table]
          apply Wp.bind' (Q := fun _ h' => h' = e.hc (ca'.set! (e.oc + k + s.huff.toNat) ⟨64, (s.len - s.drop).toUInt8, 0⟩))
          · apply Wp.bind' (wp_add e ca' (e.oc + k) s.huff.toNat (by omega))
            rintro q h' ⟨rfl, rfl⟩
            refine ⟨(), _, Ptr.store_ok (e.get_hc ca') e.h_ro (by omega), ?_⟩
            rw [Env.hc_hc]
          · rintro _ h' rfl
            apply Wp.bind' (wp_add e _ e.oc s.used.toNat (by rw [Array.size_set!]; omega))
            rintro q h' ⟨rfl, rfl⟩
            have hne0 : s.huff.toNat ≠ 0 := fun h0 => hh0 (UInt32.toNat_inj.mp (by rw [h0]; rfl))
            obtain ⟨hm1, hRR, hh1, hnxt⟩ := hinc hne0
            have hk0 : k = 0 := by
              have := Ptr.ref.inj (hn.symm.trans hnxt)
              omega
            refine Wp.pure' ⟨_, rfl, ?_, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide), fun _ => ?_, ?_, rfl⟩
            · refine ⟨by rw [Array.size_set!]; exact hf.1, fun x hx => ?_⟩
              have hne : e.oc + k + s.huff.toNat ≠ x := by omega
              rw [getElem?_set!_ne hne]
              exact hf.2 x hx
            · intro hg
              obtain ⟨hW, hL⟩ := hcF hg
              refine ⟨fun j hj mm hmm => ?_, fun a h1 h2 h3 h4 => absurd h3 (by omega)⟩
              have hj0 : j = 0 := by omega
              subst hj0
              rw [getElem?_set!_ne (by rw [gaddr0 e hm1 hRR hmm]; omega)]
              exact hW 0 (by omega) mm hmm
            · intro _
              refine ⟨s.used.toNat, rfl, endFields.1.2.2, ?_⟩
              intro single one
              have lastIndex : e.m - 1 = 0 := by omega
              have drop0 : s.drop = 0 := by
                apply UInt32.toNat_inj.mp
                have drop := endFields.2.1
                rw [lastIndex] at drop
                exact drop
              have len1 : s.len = 1 := by
                apply UInt32.toNat_inj.mp
                exact endFields.2.2.1.trans one
              simp only [hk0, hh1, Nat.add_zero, len1, drop0]
              exact getElem?_set!_self (by omega)
      · cases impossible
    · rintro s h' hinv
      rcases hinv with ⟨i, ca', rfl, hf, hmi, hexi⟩ | ⟨ca', rfl, hf, hx, hfin, hsz', hcF, hinc, endFields⟩ | impossible
      · right
        have hex : s.exit = 0 := hmi.2.1
        have hsymi : s.sym.toNat = i := hmi.2.2.1
        have hi : i < e.m := hmi.1
        obtain ⟨s2, h2, hrun, ca2, hh, hf2, ⟨hpost, hpostE, hpostF⟩, noRefusal⟩ := hereTop_wp_budget e budget i s ca' hmi hexi
        subst hh
        refine ⟨s, e.hc ca', s2, e.hc ca2, ?_, ?_, ?_, ?_⟩
        · show (pure (s.exit == 0, s) : M _) _ = _
          simp [hex]
        · rw [buildStep_eq]; exact hrun
        · rcases hpost with ⟨him, hMI⟩ | ⟨him, hx, hfin, hsz2⟩ | ⟨hx, hnc, hsz2⟩
          · exact Or.inl ⟨i + 1, ca2, rfl, hf.trans hf2, hMI, hpostE him hMI.2.1⟩
          · refine Or.inr (Or.inl ⟨ca2, rfl, hf.trans hf2, hx, hfin, hsz2, (hpostF him hx).1, (hpostF him hx).2, ?_⟩)
            obtain ⟨descriptor, drop, len⟩ := hereTop_final_descriptor hmi hexi him hrun
            have index : i = e.m - 1 := by omega
            have maxLen : e.l i = e.mx := by
              change lenAt e.f e.n i = lenAt e.f e.n (Tc e.f e.n 15 - 1)
              rw [index, hm15]
            refine ⟨?_, ?_, len.trans maxLen, ?_⟩
            · simpa only [index] using descriptor
            · simpa only [index] using drop
            · intro single one
              exact hereTop_final_single_huff hmi him single one hrun
          · exact False.elim (noRefusal hx)
        · rcases hpost with ⟨him, hMI⟩ | ⟨him, hx, hfin, hsz2⟩ | ⟨hx, hnc, hsz2⟩
          · have h3 : s2.exit = 0 := hMI.2.1
            have h4 : s2.sym.toNat = i + 1 := hMI.2.2.1
            simp only [hex, h3, ite_true, hsymi, h4]; omega
          · simp only [hx, hex]; simp; omega
          · simp only [hx, hex]; simp; omega
      · left
        refine ⟨s, e.hc ca', ?_, Or.inl ⟨ca', rfl, hf, hx, hfin, hsz', hcF, hinc, endFields⟩⟩
        show (pure (s.exit == 0, s) : M _) _ = _
        simp [hx]
      · cases impossible
    · dsimp only
      split
      · exact lt_fuel (by omega)
      · exact lt_fuel (by omega)

#print axioms itTail_cells_wp_budget

/-- The real accepted constructor environment supplies all descriptor
budgets from its default payload root and the proved mathematical bounds. -/
theorem env_default_payload_budget (e : Env)
    (defaults : (e.c.type = LENS ∧ e.n ≤ 286 ∧ e.R = max (e.l 0) (min 9 e.mx)) ∨
      (e.c.type = DISTS ∧ e.n ≤ 30 ∧ e.R = max (e.l 0) (min 6 e.mx))) :
    ∀ j, j < e.m → (e.D j).used ≤ e.cap := by
  intro j inside
  have index : j < Canon.nz e.ls := by rw [e.nz_eq]; exact inside
  rcases e.h_end with complete | single
  · have code : CompleteCode e.ls e.R e.mx := by
      refine ⟨?_, Cover.complete_of_Kc complete, e.h_R1, e.h_Rmx, ?_, ?_⟩
      · rw [e.nz_eq]; exact e.h_pos
      · change mxl e.f e.n = Canon.L (lensOf e.f e.n) (Canon.nz (lensOf e.f e.n) - 1)
        rw [Zlib.Inftrees.Proofs.nz_eq, L_eq e.f e.n (by have := e.h_pos; omega)]
        rfl
      · change Canon.L (lensOf e.f e.n) 0 ≤ e.R
        rw [L_eq e.f e.n e.h_pos]
        exact e.h_R0
    have monotone := desc_used_mono e.ls e.R e.mx (show j ≤ Canon.nz e.ls - 1 by omega)
    have count : Canon.nz e.ls ≤ e.n := by rw [e.nz_eq]; exact Tc_le 15 e.n
    have first : Canon.L e.ls 0 = e.l 0 := L_eq e.f e.n e.h_pos
    have capacity := e.h_cap
    rcases defaults with ⟨type, small, root⟩ | ⟨type, small, root⟩
    · have bound := lens_default_desc_budget code (show Canon.nz e.ls ≤ 286 by omega)
        (by rw [first]; exact root)
      rw [type] at capacity
      simp [LENS, CODES] at capacity
      change (Canon.desc e.ls e.R e.mx j).used ≤ e.cap
      omega
    · have bound := dist_default_desc_budget code (show Canon.nz e.ls ≤ 30 by omega)
        (by rw [first]; exact root)
      rw [type] at capacity
      simp [DISTS, LENS, CODES] at capacity
      change (Canon.desc e.ls e.R e.mx j).used ≤ e.cap
      omega
  · have one : e.m = 1 := single.2.1
    have rootOne : e.R = 1 := by have := e.h_Rmx; have := e.h_R1; have : e.mx = 1 := single.1; omega
    have zero : j = 0 := by omega
    rw [zero]
    change 2 ^ e.R ≤ e.cap
    rw [rootOne]
    have capacity := e.h_cap
    rcases defaults with ⟨type, _, _⟩ | ⟨type, _, _⟩
    · rw [type] at capacity
      simp [LENS, CODES] at capacity
      omega
    · rw [type] at capacity
      simp [DISTS, LENS, CODES] at capacity
      omega

/-- The translated constructor tail returns success for its real default
payload environment; all capacity tests are now discharged mathematically. -/
theorem itTail_default_payload_wp (e : Env)
    (defaults : (e.c.type = LENS ∧ e.n ≤ 286 ∧ e.R = max (e.l 0) (min 9 e.mx)) ∨
      (e.c.type = DISTS ∧ e.n ≤ 30 ∧ e.R = max (e.l 0) (min 6 e.mx)))
    (ca : Array Code) (count : Array UInt16) (bits min : UInt32) (left : Int32)
    (hcnt : CountOK e count 0) (hmin : min.toNat = e.l 0) (hsz : e.oc + e.cap ≤ ca.size) :
    Wp (itTail e.c.type e.c.lens e.c.table bits e.c.work count e.c.max min e.c.root left e.c.base e.c.extra e.c.match_) (e.hc ca)
      (fun r h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
        ((r.1 = 0 ∧ ∃ u, u ≤ e.cap ∧ r.2.1 = .ref e.rc (e.oc + u) ∧ r.2.2 = e.c.root) ∨
         (r.1 = 1 ∧ r.2.1 = e.c.table ∧ r.2.2 = bits)) ∧
        ((r.1 = 1 → e.c.type ≠ CODES) ∧ (r.1 = 0 → Cont e e.m e.m ca')) ∧ r.1 ≠ 1) := by
  obtain ⟨result, after, run, ca', heap, frame, ret, noCodes, contents, details, zero⟩ :=
    itTail_cells_wp_budget e (env_default_payload_budget e defaults) ca count bits min left hcnt hmin hsz
  exact ⟨result, after, run, ca', heap, frame, ret, ⟨noCodes, contents⟩, by rw [zero]; decide⟩

#print axioms env_default_payload_budget
#print axioms itTail_default_payload_wp


private theorem pure_no_refusal_wp
    {value : Int32 × CodePtr × UInt32} {h : Heap}
    {Q : (Int32 × CodePtr × UInt32) → Heap → Prop}
    (refusal : value.1 ≠ 1) (previous : Wp (pure value) h Q) :
    Wp (pure value) h (fun r after => Q r after ∧ r.1 ≠ 1) := by
  obtain ⟨result, after, run, post⟩ := previous
  change Except.ok (value, h) = Except.ok (result, after) at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
  exact ⟨value, h, rfl, post, refusal⟩

theorem itB_default_payload_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max min root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmax : max.toNat = mxl P.f codes.toNat) (hpos : 0 < Tc P.f codes.toNat 15)
    (hmin : min.toNat = lenAt P.f codes.toNat 0)
    (hr1 : 1 ≤ root.toNat) (hr0 : lenAt P.f codes.toNat 0 ≤ root.toNat) (hrm : root.toNat ≤ mxl P.f codes.toNat)
    (hrC : type = CODES → root.toNat = mxl P.f codes.toNat)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ root.toNat = Max.max (lenAt P.f codes.toNat 0) (Min.min 9 (mxl P.f codes.toNat))) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ root.toNat = Max.max (lenAt P.f codes.toNat 0) (Min.min 6 (mxl P.f codes.toNat)))) :
    Wp (itB type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max min root) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧ r.1 ≠ 1) := by
  unfold itB
  apply Wp.bind' (kraft_loop P.f codes.toNat count hcs hcc h)
  rintro ⟨left, bad, len⟩ h' ⟨rfl, hk⟩
  dsimp only at hk ⊢
  by_cases hbad : bad = true
  · rw [ite_eq_left hbad]
    have hnf : ¬ Fits P.f codes.toNat := by
      rcases hk with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd (hbad.symm.trans h1) (by decide)
    apply pure_no_refusal_wp (by change (-1 : Int32) ≠ 1; decide)
    exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
      fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
      fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ hacc => hnf hacc.1⟩
  · rw [ite_eq_right hbad]
    have hbad' : bad = false := by simpa using hbad
    obtain ⟨hfit, hleft⟩ : Fits P.f codes.toNat ∧ left.toInt = 2 ^ 15 - (Kc P.f codes.toNat 15 : Int) := by
      rcases hk with ⟨h1, _⟩ | ⟨_, h2, h3⟩
      · exact absurd h1 hbad
      · exact ⟨h2, h3⟩
    have hK15 := hfit 15 (by omega) (by omega)
    by_cases hg : (decide (left > 0) && (type == CODES || max != 1)) = true
    · rw [ite_eq_left hg]
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
      apply pure_no_refusal_wp (by change (-1 : Int32) ≠ 1; decide)
      exact Wp.pure' ⟨Result.unchanged P.hgw P.hgc ⟨Or.inr rfl, rfl, rfl⟩,
        fun h => absurd (show (-1 : Int32) = 0 from h) (by decide),
        fun h => absurd (show (-1 : Int32) = 1 from h) (by decide), fun _ => hnacc⟩
    · rw [ite_eq_right hg]
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
              RetInfo type P.f codes.toNat r) ∧ r.1 ≠ 1) := by
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
        have := itTail_default_payload_wp e (show (e.c.type = LENS ∧ e.n ≤ 286 ∧ e.R = Max.max (e.l 0) (Min.min 9 e.mx)) ∨
            (e.c.type = DISTS ∧ e.n ≤ 30 ∧ e.R = Max.max (e.l 0) (Min.min 6 e.mx)) from defaults) P.ca count bits min left hcnt0 hmin P.hca
        rw [hhc] at this
        refine Wp.mono this ?_
        rintro r h3 ⟨ca', rfl, hf, hr, hrne, noRefusal⟩
        refine ⟨?_, noRefusal⟩
        have hacc : Acc type P.f codes.toNat := by
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
      rcases P.hty with ht | ht | ht
      · subst ht
        rw [ite_eq_left (by decide)]
        exact key #[] #[] 20 (fun _ => rfl) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      · subst ht
        rw [ite_eq_right (by decide), ite_eq_left (by decide)]
        exact key lbase lext 257 (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩) (fun h => absurd h (by decide))
      · subst ht
        rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
        exact key dbase dext 0 (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩)


#print axioms itB_default_payload_wp
theorem itA_default_payload_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (count : Array UInt16) (max root : UInt32)
    (hcs : count.size = 16) (hcc : ∀ l, 1 ≤ l → l ≤ 15 → (count.getD l 0).toNat = cnt P.f codes.toNat l)
    (hmaxq : (Tc P.f codes.toNat 15 = 0 ∧ max.toNat = 0) ∨ (0 < Tc P.f codes.toNat 15 ∧ max.toNat = mxl P.f codes.toNat))
    (hroot : root.toNat ≤ max.toNat) (hrC : type = CODES → root.toNat = max.toNat)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ root.toNat = Min.min 9 max.toNat) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ root.toNat = Min.min 6 max.toNat)) :
    Wp (itA type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow) count max root) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧ r.1 ≠ 1) := by
  unfold itA
  by_cases hm0 : (max == 0) = true
  · rw [ite_eq_left hm0]
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
    apply pure_no_refusal_wp (by change (0 : Int32) ≠ 1; decide)
    refine Wp.pure' ⟨⟨P.wa, (P.ca.set! oc ⟨64, 1, 0⟩).set! (oc + 1) ⟨64, 1, 0⟩, ?_, rfl, ?_, fun _ _ => rfl, ?_, Or.inl ⟨rfl, 2, hcap2, rfl⟩⟩,
      fun _ => hacc, fun h => absurd (show (0 : Int32) = 1 from h) (by decide),
      fun h => absurd (show (0 : Int32) = -1 from h) (by decide)⟩
    · rw [wput_self P.hgw]
    · simp [Array.size_set!]
    · intro x hx
      have h1 : oc + 1 ≠ x := by omega
      have h2 : oc ≠ x := by omega
      rw [getElem?_set!_ne h1, getElem?_set!_ne h2]
  · rw [ite_eq_right hm0]
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
    · rw [ite_eq_left hr]
      have hr' : root.toNat < min.toNat := UInt32.lt_iff_toNat_lt.mp hr
      exact itB_default_payload_wp P count max min min hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)
        (by
          rcases defaults with ⟨typeL, sizeL, requested⟩ | ⟨typeD, sizeD, requested⟩
          · left
            refine ⟨typeL, sizeL, ?_⟩
            rw [hmx] at requested
            omega
          · right
            refine ⟨typeD, sizeD, ?_⟩
            rw [hmx] at requested
            omega)
    · rw [ite_eq_right hr]
      have hr' : min.toNat ≤ root.toNat := by
        have := (not_congr UInt32.lt_iff_toNat_lt).mp hr; omega
      exact itB_default_payload_wp P count max min root hcs hcc hmx hpos hmin (by omega) (by omega) (by omega)
        (fun hC => by have := hrC hC; omega)
        (by
          rcases defaults with ⟨typeL, sizeL, requested⟩ | ⟨typeD, sizeD, requested⟩
          · left
            refine ⟨typeL, sizeL, ?_⟩
            rw [hmx] at requested
            omega
          · right
            refine ⟨typeD, sizeD, ?_⟩
            rw [hmx] at requested
            omega)


theorem itTop_default_payload_wp {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6)) :
    Wp (itTop type (Ptr.ref rl ol) codes (Ptr.ref rc oc) bits (Ptr.ref rw ow)) h
      (fun r h' => (Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (Ptr.ref rc oc) bits r h' ∧
        RetInfo type P.f codes.toNat r) ∧ r.1 ≠ 1) := by
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
  · rw [ite_eq_left hgt]
    exact itA_default_payload_wp P count2 max max hs2 hcc hmaxq (Nat.le_refl _) (fun _ => rfl)
      (by
        have greater : max.toNat < bits.toNat := UInt32.lt_iff_toNat_lt.mp hgt
        rcases defaults with ⟨typeL, sizeL, requested⟩ | ⟨typeD, sizeD, requested⟩
        · left
          refine ⟨typeL, sizeL, ?_⟩
          rw [requested] at greater
          change max.toNat < 9 at greater
          omega
        · right
          refine ⟨typeD, sizeD, ?_⟩
          rw [requested] at greater
          change max.toNat < 6 at greater
          omega)
  · rw [ite_eq_right hgt]
    have hle : bits.toNat ≤ max.toNat := by
      have := (not_congr UInt32.lt_iff_toNat_lt).mp hgt; omega
    exact itA_default_payload_wp P count2 max bits hs2 hcc hmaxq hle
      (fun hC => by
        obtain ⟨_, h7, hb7⟩ := P.hcodes hC
        rcases hmaxq with ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · have := mxl_le7 (f := P.f) (n := codes.toNat) a h7
          omega)
      (by
        rcases defaults with ⟨typeL, sizeL, requested⟩ | ⟨typeD, sizeD, requested⟩
        · left
          refine ⟨typeL, sizeL, ?_⟩
          rw [requested] at hle ⊢
          change 9 ≤ max.toNat at hle
          change 9 = Min.min 9 max.toNat
          omega
        · right
          refine ⟨typeD, sizeD, ?_⟩
          rw [requested] at hle ⊢
          change 6 ≤ max.toNat at hle
          change 6 = Min.min 6 max.toNat
          omega)



#print axioms itA_default_payload_wp
#print axioms itTop_default_payload_wp

/-- The real translated inflate_table call cannot report capacity refusal
for the exact default payload callers: LENS with <=286 symbols/root nine,
or DISTS with <=30 symbols/root six. Invalid alphabets may still return -1. -/
theorem inflate_table_default_payload_no_refusal
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6)) :
    ∃ result after, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (.ref rc oc) bits result after ∧
      RetInfo type P.f codes.toNat result ∧ result.1 ≠ 1 := by
  obtain ⟨result, after, run, ⟨frame, ret⟩, noRefusal⟩ := itTop_default_payload_wp P defaults
  exact ⟨result, after, by rw [C.run, inflate_table_eq]; exact run, frame, ret, noRefusal⟩

/-- At the actual default payload call, success is equivalent to the
independent acceptable-alphabet relation, including empty and singleton
cases. This is a theorem about execution, with no callee contract assumed. -/
theorem inflate_table_default_payload_success_iff
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6)) :
    ∃ result after, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 ↔ ZlibF.Spec.Acceptable (kindOf type) (lensList P.la ol codes.toNat)) ∧ result.1 ≠ 1 := by
  obtain ⟨result, after, run, frame, ⟨accepted, _, rejected⟩, noRefusal⟩ :=
    inflate_table_default_payload_no_refusal P defaults
  have accept := acc_iff type P.f codes.toNat P.hf15
  have lists : lensOf P.f codes.toNat = lensList P.la ol codes.toNat := rfl
  rw [lists] at accept
  have kinds : result.1 = 0 ∨ result.1 = 1 ∨ result.1 = -1 := by
    obtain ⟨_, _, _, _, _, _, _, returned⟩ := frame
    rcases returned with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact Or.inl zero
    · exact Or.inr (Or.inl one)
    · exact Or.inr (Or.inr bad)
  refine ⟨result, after, run, frame, ⟨fun zero => accept.mp (accepted zero), ?_⟩, noRefusal⟩
  intro valid
  rcases kinds with zero | one | bad
  · exact zero
  · exact False.elim (noRefusal one)
  · exact False.elim (rejected bad (accept.mpr valid))

/-- Legal independent payload alphabets make the actual default table
constructor return zero, with the actual frame and moved pointer retained. -/
theorem inflate_table_default_payload_success
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6))
    (valid : ZlibF.Spec.Acceptable (kindOf type) (lensList P.la ol codes.toNat)) :
    ∃ result after, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (.ref rc oc) bits result after ∧ result.1 = 0 := by
  obtain ⟨result, after, run, frame, correct, _⟩ := inflate_table_default_payload_success_iff P defaults
  exact ⟨result, after, run, frame, correct.mpr valid⟩

#print axioms inflate_table_default_payload_no_refusal
#print axioms inflate_table_default_payload_success_iff
#print axioms inflate_table_default_payload_success


/-- Default payload construction both succeeds and installs its independent
canonical decoding meaning on the same real execution. -/
theorem inflate_table_default_payload_installed
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (P : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6))
    (valid : ZlibF.Spec.Acceptable (kindOf type) (lensList P.la ol codes.toNat)) :
    ∃ result after, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat P.wa P.ca (.ref rc oc) bits result after ∧ result.1 = 0 ∧
      ∃ (ca : Array Code) (used : Nat), Space.get after rc = some ca ∧ result.2.1 = .ref rc (oc + used) ∧
        used ≤ capOf type ∧ DecodeTableInvariant.Inv type ca oc result.2.2.toNat used (lensOf P.f codes.toNat) := by
  obtain ⟨result, after, run, frame, zero⟩ := inflate_table_default_payload_success P defaults valid
  have kind : type = LENS ∨ type = DISTS := by
    rcases defaults with ⟨left, _, _⟩ | ⟨right, _, _⟩
    · exact Or.inl left
    · exact Or.inr right
  obtain ⟨other, otherHeap, otherRun, _, installed⟩ :=
    constructor_establishes_decode_table_invariant h type rl ol codes rc oc bits rw ow P kind
  rw [run] at otherRun
  cases otherRun
  exact ⟨result, after, run, frame, zero, installed zero⟩

#print axioms inflate_table_default_payload_installed

end Zlib.Inftrees.Proofs.BudgetExecution
