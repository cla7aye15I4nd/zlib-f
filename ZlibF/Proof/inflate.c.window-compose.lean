import ZlibF.Proof.«inflate.c.window-general»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem uw_main_public {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eo : Nat} {source : BRef}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hwb : st.wbits.toNat ≤ 15) (hasz : a.size = 2 ^ st.wbits.toNat)
    (hws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat)
    (hwn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0))
    (heb : Space.get H source = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    updatewindow (some r) (.ref source eo) copy H = .ok (0, setI
      { setI H zs (initWinS st) with bytes := upd H.bytes w (some (uwPost (initWinS st) a ebytes eo copy).1) } zs
      (uwPost (initWinS st) a ebytes eo copy).2) := by
  have hpow := shl_toNat_aux hwb
  have h2pos := Nat.two_pow_pos st.wbits.toNat
  have hcase : (st.wsize = 0 ∧ initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 }) ∨
      (st.wsize ≠ 0 ∧ initWinS st = st) := by
    by_cases h0 : st.wsize = 0
    · left; exact ⟨h0, by simp [initWinS, h0]⟩
    · right; exact ⟨h0, by simp [initWinS, h0]⟩
  have hpos : (initWinS st).wsize ≠ 0 ∧ (initWinS st).wsize.toNat = 2 ^ st.wbits.toNat ∧ (initWinS st).wnext.toNat < (initWinS st).wsize.toNat := by
    rcases hcase with ⟨h0, e⟩ | ⟨h0, e⟩
    · rw [e]
      have hz0 : ((1 : UInt32) <<< st.wbits).toNat = 2 ^ st.wbits.toNat := hpow
      refine ⟨fun hh => ?_, hz0, ?_⟩
      · have h0' : ((1 : UInt32) <<< st.wbits).toNat = 0 := by
          have hh' : ((1 : UInt32) <<< st.wbits) = 0 := hh
          rw [hh']; rfl
        omega
      · show (0 : UInt32).toNat < ((1 : UInt32) <<< st.wbits).toNat
        rw [hz0]; simp; omega
    · rw [e]
      have : st.wsize.toNat ≠ 0 := fun hh => h0 (UInt32.toNat_inj.mp (by simpa using hh))
      refine ⟨h0, by omega, by omega⟩
  have hfull := hpos.2.1
  have hsz1 : (initWinS st).wsize.toNat ≤ a.size := by omega
  have hwn1 := hpos.2.2
  have hpos := hpos.1
  have hL1 : Live (setI H zs (initWinS st)) r zs z (initWinS st) :=
    ⟨by simpa using hL.hz, by simp, hL.zst, by unfold initWinS; split <;> exact hL.back, by unfold initWinS; split <;> exact hL.mode,
      hL.zalloc, hL.zfree⟩
  have hw1 : (initWinS st).window = .ref (.blk w) 0 := by unfold initWinS; split <;> exact hw
  rw [uw_init hL hw hwb]
  have ha1 : (setI H zs (initWinS st)).bytes w = some a := ha
  have hro1 : (setI H zs (initWinS st)).ro w = false := hro
  have heb1 : Space.get (setI H zs (initWinS st)) source = some ebytes := by
    cases source with
    | str i => exact (C.LibcBorrow.str_view_stable
        (before := H) (after := setI H zs (initWinS st)) (i := i) (Or.inr rfl)).trans heb
    | _ => simpa [Space.get, setI] using heb
  have hsep1 : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      (initWinS st).window (initWinS st).wsize.toNat := by
    simpa only [hw1, hw, hfull] using hsep
  by_cases hbig : (initWinS st).wsize ≤ copy
  · have := uw_core_big_public hL1 hw1 ha1 hro1 hpos hsz1 heb1 hc hoff hsep1 hbig
    simpa [uwPost, hbig] using this
  · by_cases hP : (initWinS st).wsize - (initWinS st).wnext > copy
    · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
        have : ¬ (initWinS st).wsize ≤ copy := hbig
        rw [UInt32.le_iff_toNat_le] at this; omega
      have := uw_core_small1_public hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hc hoff hsep1 hbig hP
      simpa [uwPost, hbig, hP] using this
    · by_cases hR : copy - ((initWinS st).wsize - (initWinS st).wnext) = 0
      · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
          have : ¬ (initWinS st).wsize ≤ copy := hbig
          rw [UInt32.le_iff_toNat_le] at this; omega
        have := uw_core_small3_public hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hc hoff hsep1 hbig hP hR
        simpa [uwPost, hbig, hP, hR] using this
      · have hlt : copy.toNat < (initWinS st).wsize.toNat := by
          have : ¬ (initWinS st).wsize ≤ copy := hbig
          rw [UInt32.le_iff_toNat_le] at this; omega
        have := uw_core_small2_public hL1 hw1 ha1 hro1 hpos hsz1 hwn1 heb1 hc hoff hsep1 hbig hP hR
        simpa [uwPost, hbig, hP, hR] using this

theorem uw_post_public {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eo : Nat} {source : BRef}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hG : Good H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hasz : a.size = 2 ^ st.wbits.toNat)
    (heb : Space.get H source = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    ∃ H' st', updatewindow (some r) (.ref source eo) copy H = .ok (0, H') ∧
      H' = setI { setI H zs (initWinS st) with bytes := upd H.bytes w (some (uwPost (initWinS st) a ebytes eo copy).1) } zs st' ∧
      st' = (uwPost (initWinS st) a ebytes eo copy).2 ∧ Good H' r zs z st' ∧ st'.window = st.window ∧
      H'.bytes w = some (uwPost (initWinS st) a ebytes eo copy).1 ∧ (uwPost (initWinS st) a ebytes eo copy).1.size = a.size ∧
      (∀ b, b ≠ w → H'.bytes b = H.bytes b) ∧ (∀ b, H'.live b ↔ H.live b) ∧ H'.nextBlk = H.nextBlk := by
  have hL := hG.live
  have hI := hG.inv
  have hmain := uw_main_public hL hw ha hro hI.win.wbits hasz hI.win.ws hI.win.wn heb hc hoff hsep
  obtain ⟨f1, f2, f3, hv1, hwn1, heq1, f4, f5, f6, f7, f8, f16, f17, f18, f12, f13⟩ :=
    initWinS_facts hI.win.wbits hI.win.ws hI.win.hv hI.win.wn hI.win.eq
  have hwb := hI.win.wbits
  have hle : (initWinS st).wsize.toNat ≤ 2 ^ 16 := by
    rw [f1]; have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : st.wbits.toNat ≤ 16); omega
  have hposn : (initWinS st).wsize.toNat ≠ 0 := by rw [f1]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, gv, gwn, geq⟩ :=
    uwPost_arith (st := initWinS st) (a := a) (ebytes := ebytes) (eo := eo) (copy := copy) hposn hv1 hwn1 heq1 copy.toNat_lt hle
  have hAsz := uwPost_size (initWinS st) a ebytes eo copy
  generalize hP : uwPost (initWinS st) a ebytes eo copy = P at *
  have hs1 : (setI H zs (initWinS st)).istates zs = some (initWinS st) := by simp
  have hbw : (setI H zs (initWinS st)).bytes w = some a := ha
  have hS : Shape H { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } :=
    (shape_setI hL.hs _).trans (shape_setB (h := setI H zs (initWinS st)) hbw P.1)
  have hS2 : Shape H (setI { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } zs P.2) :=
    hS.trans (shape_setI (s0 := initWinS st) (by simp) _)
  have hz0 : r.get { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } = some z := by
    cases r <;> simpa [ZStreamRef.get] using hL.hz
  have hs0 : ({ setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } : Heap).istates zs = some (initWinS st) := by
    simp
  have hUh : Uniq { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } := hS.uniq hG.uniq
  have hFh : Fresh { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } := hS.fresh (by simp) hG.fresh
  have hstI : StInv { setI H zs (initWinS st) with bytes := upd H.bytes w (some P.1) } zs P.2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨w1, w2, w3⟩ := hI.wf
      exact ⟨by rw [g9, f16]; exact w1, by rw [g10, f17]; exact w2, by rw [g11, f18]; exact w3⟩
    · refine ⟨by rw [g2, f2]; exact hI.win.wbits, Or.inr ⟨w, P.1, by rw [g3, f3]; exact hw, by simp, by simpa using hro, ?_⟩,
        fun h0 => ?_, ?_, gv, Or.inl gwn, geq⟩
      · rw [g2, f2, hAsz, hasz]
      · rw [g3, f3, hw] at h0; cases h0
      · rw [g1, f1, g2, f2]; right; rfl
    · rw [g4, f4]; exact hI.reqbits
    · rw [g5, f5]; exact hI.bits
    · unfold PtrInv; rw [g6, f6, g7, f7, g8, f8]; exact hI.ptr
  refine ⟨_, P.2, hmain, rfl, rfl, ?_, by rw [g3, f3], by simp, hAsz, ?_, fun b => hS2.live b, by simp⟩
  · have := good_set hz0 hs0 hUh hFh hL.zst hL.zalloc hL.zfree (by rw [g12, f12]; exact hL.back)
      (by rw [g13, f13]; exact hL.mode) hstI
    rwa [ZStreamRef.put_self hz0] at this
  · intro b hb; simp [upd_ne _ _ _ _ hb]

theorem uw_null_ok_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {eo : Nat} {source : BRef}
    {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ H' st', updatewindow (some r) (.ref source eo) copy h = .ok (0, H') ∧ Good H' r zs z st' ∧
      st'.window = .ref (.blk h.nextBlk) 0 ∧ (∃ A, H'.bytes h.nextBlk = some A) ∧
      (∀ S, h.Owns S → H'.Owns (fun b => S b ∨ b = h.nextBlk)) ∧ H'.nextBlk = h.nextBlk + 1 ∧
      (∀ b, b ≠ h.nextBlk → H'.bytes b = h.bytes b) := by
  have hL := hG.live
  have hI := hG.inv
  have hF := hG.fresh
  have hne : source ≠ .blk h.nextBlk := by
    intro he
    subst source
    have hfresh := Fresh.bytes hF (b := h.nextBlk) (Nat.le_refl _)
    have hbytes : h.bytes h.nextBlk = some ebytes := by simpa using heb
    rw [hbytes] at hfresh
    cases hfresh
  rw [uw_alloc_ok hL hza hI.win.wbits hw hok hF]
  have hn : ((1 <<< st.wbits : UInt32) * 1).toNat = 2 ^ st.wbits.toNat := by
    have := shl_toNat_aux hI.win.wbits
    simpa using this
  obtain ⟨A0, hA0⟩ : ∃ A0 : Array UInt8, A0 = Array.ofFn (n := ((1 <<< st.wbits : UInt32) * 1).toNat)
      fun i => Junk.of (h.garbage h.nalloc i.val) := ⟨_, rfl⟩
  have hA0sz : A0.size = 2 ^ st.wbits.toNat := by rw [hA0, Array.size_ofFn]; exact hn
  have hws0 := hI.win.nullws hw
  have hws0n : st.wsize.toNat = 0 := by rw [hws0]; rfl
  have hA := Zlib.Zutil.Proofs.allocHeap_frame h ((1 <<< st.wbits : UInt32) * 1).toNat
  have hAb : (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat).bytes h.nextBlk = some A0 := by
    rw [hA0]; simp [Zlib.Zutil.Proofs.allocHeap]
  have hAro : (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat).ro h.nextBlk = false := by
    simp [Zlib.Zutil.Proofs.allocHeap]
  have hS : Shape (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat)
      (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk)) :=
    shape_setI (s0 := st) (by simpa [Zlib.Zutil.Proofs.allocHeap] using hL.hs) _
  have hUa := uniq_allocHeap hG.uniq hF ((1 <<< st.wbits : UInt32) * 1).toNat
  have hFa := hA.2.1 hF
  have hG2 : Good (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk))
      r zs z (withWin st h.nextBlk) := by
    refine ⟨⟨?_, by simp, hL.zst, hL.back, hL.mode, hL.zalloc, hL.zfree⟩, ?_, hS.uniq hUa, hS.fresh rfl hFa⟩
    · cases r <;> simpa [ZStreamRef.get, Zlib.Zutil.Proofs.allocHeap, setI] using hL.hz
    · refine ⟨hI.wf, ⟨hI.win.wbits, Or.inr ⟨h.nextBlk, A0, rfl, ?_, ?_, ?_⟩, fun h0 => absurd h0 (by simp [withWin]), ?_, ?_, ?_, ?_⟩,
        hI.reqbits, hI.bits, hI.ptr⟩
      · simpa [setI] using hAb
      · simpa [setI] using hAro
      · exact hA0sz
      · exact Or.inl hws0n
      · have := hI.win.hv; show st.whave.toNat ≤ st.wsize.toNat; exact this
      · right; refine ⟨hws0n, ?_⟩
        have := hI.win.wn; show st.wnext.toNat = 0; omega
      · intro hh; have := hI.win.hv; show st.wnext.toNat = st.whave.toNat; have := hI.win.wn; have := hI.win.hv
        change st.whave.toNat < st.wsize.toNat at hh; omega
  have hz2 : r.get (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk)) = some z :=
    hG2.live.hz
  have hbe : Space.get (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs
      (withWin st h.nextBlk)) source = some ebytes := by
    cases source with
    | blk b =>
      have hbn : b ≠ h.nextBlk := fun he => hne (by cases he; rfl)
      simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ hbn] using heb
    | str b => exact (C.LibcBorrow.str_view_stable
        (before := h) (after := setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat)
          zs (withWin st h.nextBlk)) (i := b) (Or.inr rfl)).trans heb
    | st_dist_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | st_length_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | dstate_depth b => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
  have hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      (withWin st h.nextBlk).window (2 ^ (withWin st h.nextBlk).wbits.toNat) := by
    simp [ZlibF.Spec.Public.Separate, withWin, hne]
  obtain ⟨H', st', hrun, -, hst', hG', hw', hb', hsz', hbo, hlive, hnb⟩ :=
    uw_post_public (hG := hG2) (w := h.nextBlk) (source := source) (eo := eo)
      (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb)
      (by simpa [setI] using hAro) (by exact hA0sz) hbe hc hoff hsep
  refine ⟨H', st', hrun, hG', by rw [hw']; rfl, ⟨_, hb'⟩, ?_, ?_, ?_⟩
  · intro S hO
    have h2 := hS.owns (hA.1 S hO)
    exact fun b => (hlive b).trans (h2 b)
  · rw [hnb]; simp [Zlib.Zutil.Proofs.allocHeap, setI]
  · intro b hb; rw [hbo b (by exact hb)]; simp [Zlib.Zutil.Proofs.allocHeap, setI, upd_ne _ _ _ _ hb]

theorem updatewindow_safe_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {eo : Nat} {source : BRef}
    {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    ∃ v h' st', C.run (updatewindow (some r) (.ref source eo) copy) h = .ok (v, h') ∧ Good h' r zs z st' ∧
      ((v = 0 ∧ st'.window ≠ .null ∧
          (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ (st.window = .null ∧ b = h.nextBlk)))) ∨
       (v = 1 ∧ st.window = .null ∧ ¬ h.allocOk h.nalloc = true ∧ h' = setI { h with nalloc := h.nalloc + 1 } zs st ∧ st' = st)) := by
  have hL := hG.live
  have hI := hG.inv
  rcases hI.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨H', st', hrun, hG', hw', -, hO, -, -⟩ := uw_null_ok_public hG hza hw hok heb hc hoff
      refine ⟨0, H', st', hrun, hG', Or.inl ⟨0 |> fun _ => rfl, by rw [hw']; simp, ?_⟩⟩
      intro S hOw
      have := hO S hOw
      simpa [hw] using this
    · have hrun := uw_alloc_fail hL hza hI.win.wbits hw hok (.ref source eo) copy
      refine ⟨1, _, st, hrun, ?_, Or.inr ⟨rfl, hw, hok, rfl, rfl⟩⟩
      have hS : Shape h { h with nalloc := h.nalloc + 1 } := Shape.refl h
      have := good_set (h0 := { h with nalloc := h.nalloc + 1 }) (z0 := z) (z' := z) (s0 := st) (st' := st) hL.hz hL.hs
        hG.uniq hG.fresh hL.zst hL.zalloc hL.zfree hL.back hL.mode (StInv.congr (h := h) rfl rfl hI)
      have hz' : r.get { h with nalloc := h.nalloc + 1 } = some z := by cases r <;> simpa [ZStreamRef.get] using hL.hz
      rwa [ZStreamRef.put_self hz'] at this
  · obtain ⟨H', st', hrun, -, -, hG', hw', -, -, -, hlive, -⟩ := uw_post_public hG hw ha hro hasz heb hc hoff hsep
    refine ⟨0, H', st', hrun, hG', Or.inl ⟨rfl, by rw [hw', hw]; simp, ?_⟩⟩
    intro S hO b
    rw [hlive b, hO b]
    simp [hw]

#print axioms updatewindow_safe_public
#print axioms uw_null_ok_public
#print axioms uw_post_public
#print axioms uw_main_public
end Zlib.Inflate.Proofs
