import ZlibF.Proof.«inftrees.c.main»
import ZlibF.Proof.«inftrees.c.final-layout»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec
set_option autoImplicit false

def EndFields (e : Env) (s : TS) : Prop :=
  DescB e (e.m - 1) s ∧ s.drop.toNat = (e.D (e.m - 1)).drop ∧
    s.len.toNat = e.mx ∧ (e.m = 1 → e.mx = 1 → s.huff = 1)

def TailDetails (e : Env) (r : Int32 × CodePtr × UInt32) (ca : Array Code) : Prop :=
  r.1 = 0 → ∃ used, r.2.1 = .ref e.rc (e.oc + used) ∧
    used = (e.D (e.m - 1)).used ∧
    (e.m = 1 → e.mx = 1 → ca[e.oc + 1]? = some ⟨64, 1, 0⟩)

theorem itTail_cells_wp (e : Env) (ca : Array Code) (count : Array UInt16) (bits min : UInt32) (left : Int32)
    (hcnt : CountOK e count 0) (hmin : min.toNat = e.l 0) (hsz : e.oc + e.cap ≤ ca.size) :
    Wp (itTail e.c.type e.c.lens e.c.table bits e.c.work count e.c.max min e.c.root left e.c.base e.c.extra
        e.c.match_) (e.hc ca)
      (fun r h' => ∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧
        ((r.1 = 0 ∧ ∃ u, u ≤ e.cap ∧ r.2.1 = .ref e.rc (e.oc + u) ∧ r.2.2 = e.c.root) ∨
         (r.1 = 1 ∧ r.2.1 = e.c.table ∧ r.2.2 = bits)) ∧ (r.1 = 1 → e.c.type ≠ CODES) ∧
        (r.1 = 0 → Cont e e.m e.m ca') ∧ TailDetails e r ca') := by
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
  by_cases hb : tooBig e.c.type (1 <<< e.c.root) = true
  · rw [ite_eq_left hb]
    exact Wp.pure' ⟨ca, rfl, ⟨rfl, fun _ _ => rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩,
      fun _ => tooBig_ne hb, (fun h => by cases h), (fun h => by cases h)⟩
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
        (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))
      (Wp.cwhile
        (fun (s : TS) h' => (∃ i ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ MI e i s ca' ∧ Ex e i s ca') ∨
          (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 1 ∧ Final e s ∧ e.oc + e.cap ≤ ca'.size ∧
            Cont e e.m e.m ca' ∧ (s.huff.toNat ≠ 0 → Einc e s) ∧ EndFields e s) ∨
          (∃ ca', h' = e.hc ca' ∧ FrameCA e ca ca' ∧ s.exit = 2 ∧ e.c.type ≠ CODES ∧ e.oc + e.cap ≤ ca'.size))
        (fun (s : TS) => if s.exit = 0 then e.m + 1 - s.sym.toNat else 0) _ ?_ (Or.inl ⟨0, ca, rfl, ⟨rfl, fun _ _ => rfl⟩, hMI0, hEx0⟩) ?_)
    · rintro s h' hinv
      rcases hinv with ⟨ca', rfl, hf, hx, hfin, hsz', hcF, hinc, endFields⟩ | ⟨ca', rfl, hf, hx, hnc, hsz'⟩
      · rw [ite_eq_right (by simp [hx])]
        obtain ⟨⟨k, hn, hk⟩, hucap, hh⟩ := hfin
        by_cases hh0 : s.huff = 0
        · rw [ite_eq_right (by simp [hh0])]
          show Wp (do let table ← Ptr.add e.c.table ↑s.used.toNat; pure (0, table, e.c.root)) _ _
          rw [e.h_table]
          apply Wp.bind' (wp_add e ca' e.oc s.used.toNat (by omega))
          rintro q h' ⟨rfl, rfl⟩
          refine Wp.pure' ⟨ca', rfl, hf, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide), fun _ => hcF, ?_⟩
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
            refine Wp.pure' ⟨_, rfl, ?_, Or.inl ⟨rfl, s.used.toNat, hucap, rfl, rfl⟩, fun h => absurd (show (0 : Int32) = 1 from h) (by decide), fun _ => ?_, ?_⟩
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
      · rw [ite_eq_left (by simp [hx])]
        exact Wp.pure' ⟨ca', rfl, hf, Or.inr ⟨rfl, rfl, rfl⟩,
          fun _ => hnc, (fun h => by cases h), (fun h => by cases h)⟩
    · rintro s h' hinv
      rcases hinv with ⟨i, ca', rfl, hf, hmi, hexi⟩ | ⟨ca', rfl, hf, hx, hfin, hsz', hcF, hinc, endFields⟩ | ⟨ca', rfl, hf, hx, hnc, hsz'⟩
      · right
        have hex : s.exit = 0 := hmi.2.1
        have hsymi : s.sym.toNat = i := hmi.2.2.1
        have hi : i < e.m := hmi.1
        obtain ⟨s2, h2, hrun, ca2, hh, hf2, hpost, hpostE, hpostF⟩ := hereTop_wp e i s ca' hmi hexi
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
          · exact Or.inr (Or.inr ⟨ca2, rfl, hf.trans hf2, hx, hnc, hsz2⟩)
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
      · left
        refine ⟨s, e.hc ca', ?_, Or.inr ⟨ca', rfl, hf, hx, hnc, hsz'⟩⟩
        show (pure (s.exit == 0, s) : M _) _ = _
        simp [hx]
    · dsimp only
      split
      · exact lt_fuel (by omega)
      · exact lt_fuel (by omega)

end Zlib.Inftrees.Proofs
