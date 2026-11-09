import ZlibF.Proof.«inflate.c.window-public-ring»
import ZlibF.Spec.Public.Lifecycle

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public

private theorem uwPost_mode (s : InflateState) (a b : Array UInt8) (eo : Nat) (n : UInt32) :
    (uwPost (initWinS s) a b eo n).2.mode = s.mode := by
  have hh : (uwPost (initWinS s) a b eo n).2 =
      { s with
        window := (uwPost (initWinS s) a b eo n).2.window
        wsize := (uwPost (initWinS s) a b eo n).2.wsize
        whave := (uwPost (initWinS s) a b eo n).2.whave
        wnext := (uwPost (initWinS s) a b eo n).2.wnext } := by
    unfold uwPost initWinS
    repeat' split
    all_goals rfl
  have hm := congrArg InflateState.mode hh
  exact hm

/-- An existing-window update changes only the owned state and window blocks. -/
theorem uw_existing_frame {h : Heap} {r : ZStreamRef} {zs w : Nat} {st st0 st1 : InflateState}
    {a : Array UInt8} (hw : st.window = .ref (.blk w) 0) :
    Frame h (setI { setI h zs st0 with bytes := upd h.bytes w (some a) } zs st1)
      (fun b => StreamRoot r b ∨ InflateOwned zs st b) := by
  simp only [Frame, setI, true_and]
  refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ hb
  have hi : b ≠ zs := fun he => hb (Or.inr (Or.inl he))
  have hw' : b ≠ w := fun he => hb (Or.inr (Or.inr (by simpa [hw] using he.symm)))
  simp [upd_ne, hi, hw']

/-- A new-window update changes only the owned state among pre-existing
objects; the allocated block was not live before the call. -/
theorem uw_new_frame {h : Heap} {r : ZStreamRef} {zs n : Nat} {st st0 st1 st2 : InflateState}
    {a : Array UInt8} (hf : Fresh h) :
    let alloc := Zlib.Zutil.Proofs.allocHeap h n
    let prior := setI alloc zs st0
    Frame h (setI { setI prior zs st1 with bytes := upd prior.bytes h.nextBlk (some a) } zs st2)
      (fun b => StreamRoot r b ∨ InflateOwned zs st b) := by
  dsimp only
  simp only [Frame, setI, Zlib.Zutil.Proofs.allocHeap, true_and]
  refine ⟨Nat.le_succ _, Nat.le_succ _, ?_⟩
  intro b hl hb
  have hi : b ≠ zs := fun he => hb (Or.inr (Or.inl he))
  have hn : b ≠ h.nextBlk := fun he => hf b (by omega) hl
  simp [upd_ne, hi, hn]

/-- Allocation followed by a successful window update preserves the stream mode. -/
theorem uw_null_mode_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {eo : Nat} {source : BRef} {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ after state, updatewindow (some r) (.ref source eo) copy h = .ok (0, after) ∧
      Good after r zs z state ∧ state.mode = st.mode := by
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
  obtain ⟨after, state, hr, _, hstate, hgood, _, _, _, _, _, _⟩ :=
    uw_post_public (hG := hG2) (w := h.nextBlk) (source := source) (eo := eo)
      (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb)
      (by simpa [setI] using hAro) hA0sz hbe hc hoff hsep
  refine ⟨after, state, hr, hgood, ?_⟩
  rw [hstate, uwPost_mode]
  rfl

/-- Allocation followed by an update preserves the public frame of every
pre-existing unowned object. -/
theorem uw_null_frame_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {eo : Nat} {source : BRef} {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ after state, updatewindow (some r) (.ref source eo) copy h = .ok (0, after) ∧
      Good after r zs z state ∧ Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs st b) := by
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
  obtain ⟨after, state, hr, he, _, hgood, _, _, _, _, _, _⟩ :=
    uw_post_public (hG := hG2) (w := h.nextBlk) (source := source) (eo := eo)
      (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb)
      (by simpa [setI] using hAro) hA0sz hbe hc hoff hsep
  refine ⟨after, state, hr, hgood, ?_⟩
  rw [he]
  exact uw_new_frame hF

/-- A successful `updatewindow` preserves the stream mode for all readable
sources permitted by the public range-separation condition. -/
theorem updatewindow_mode_public {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st state : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (hg : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc")
    (hsrc : Space.get h source = some bytes) (hfit : off + copy.toNat ≤ bytes.size)
    (hsep : Separate (.ref source off) copy.toNat st.window (2 ^ st.wbits.toNat))
    (hr : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after))
    (hstate : after.istates zs = some state) : state.mode = st.mode := by
  change updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) at hr
  have hsep' : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      st.window (2 ^ st.wbits.toNat) := by simpa using hsep
  rcases hg.inv.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨result, s', hrun, hgood, hmode⟩ :=
        uw_null_mode_public (copy := copy) (eo := off + copy.toNat) hg hza hw hok hsrc (by omega) hfit
      have he : after = result := by rw [hr] at hrun; cases hrun; rfl
      subst result
      have hs : state = s' := Option.some.inj (hstate.symm.trans hgood.live.hs)
      simpa [hs] using hmode
    · have hfail := uw_alloc_fail hg.live hza hg.inv.win.wbits hw hok
        (.ref source (off + copy.toNat)) copy
      rw [hr] at hfail
      cases hfail
  · obtain ⟨result, s', hrun, _, hs', hgood, _, _, _, _, _, _⟩ :=
      uw_post_public (copy := copy) (eo := off + copy.toNat) hg hw ha hro hasz hsrc (by omega) hfit hsep'
    have he : after = result := by rw [hr] at hrun; cases hrun; rfl
    have hgood' : Good after r zs z s' := by rw [he]; exact hgood
    have hs : state = s' := Option.some.inj (hstate.symm.trans hgood'.live.hs)
    rw [hs, hs', uwPost_mode]

/-- A successful `updatewindow` preserves the public frame. -/
theorem updatewindow_frame_public {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (hg : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc")
    (hsrc : Space.get h source = some bytes) (hfit : off + copy.toNat ≤ bytes.size)
    (hsep : Separate (.ref source off) copy.toNat st.window (2 ^ st.wbits.toNat))
    (hr : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after)) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs st b) := by
  change updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) at hr
  have hsep' : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      st.window (2 ^ st.wbits.toNat) := by simpa using hsep
  rcases hg.inv.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨result, _, hrun, _, hframe⟩ :=
        uw_null_frame_public (copy := copy) (eo := off + copy.toNat) hg hza hw hok hsrc (by omega) hfit
      have he : after = result := by rw [hr] at hrun; cases hrun; rfl
      simpa [he] using hframe
    · have hfail := uw_alloc_fail hg.live hza hg.inv.win.wbits hw hok
        (.ref source (off + copy.toNat)) copy
      rw [hr] at hfail
      cases hfail
  · obtain ⟨result, s', hrun, he, _, _, _, _, _, _, _, _⟩ :=
      uw_post_public (copy := copy) (eo := off + copy.toNat) hg hw ha hro hasz hsrc (by omega) hfit hsep'
    have heq : after = result := by rw [hr] at hrun; cases hrun; rfl
    rw [heq, he]
    exact uw_existing_frame hw

/-- A successful `updatewindow` retains all existing objects and allocates
only its new owned window, if one was needed. -/
theorem updatewindow_live_public {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st state : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (hg : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc")
    (hsrc : Space.get h source = some bytes) (hfit : off + copy.toNat ≤ bytes.size)
    (hsep : Separate (.ref source off) copy.toNat st.window (2 ^ st.wbits.toNat))
    (hr : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after))
    (hstate : after.istates zs = some state) :
    LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  change updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) at hr
  have hzs : h.live zs := by simp [Heap.live, hg.live.hs]
  have hsep' : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      st.window (2 ^ st.wbits.toNat) := by simpa using hsep
  rcases hg.inv.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨result, s', hrun, hgood, hwin, _, hown, _, _⟩ :=
        uw_null_ok_public (copy := copy) (eo := off + copy.toNat) hg hza hw hok hsrc (by omega) hfit
      have he : after = result := by rw [hr] at hrun; cases hrun; rfl
      subst result
      have hs : state = s' := Option.some.inj (hstate.symm.trans hgood.live.hs)
      subst state
      have ho := hown (fun b => h.live b) (fun _ => Iff.rfl)
      intro b
      have hl : after.live b ↔ h.live b ∨ b = h.nextBlk := ho b
      by_cases hb : h.live b
      · simp [LiveChange, hb, hl.mpr (Or.inl hb)]
      · have hbi : b ≠ zs := fun he => hb (he ▸ hzs)
        have hwnd : InflateOwned zs s' b ↔ b = h.nextBlk := by
          simp [InflateOwned, hwin, hbi, eq_comm]
        simpa [LiveChange, hb, hwnd] using hl
    · have hfail := uw_alloc_fail hg.live hza hg.inv.win.wbits hw hok
        (.ref source (off + copy.toNat)) copy
      rw [hr] at hfail
      cases hfail
  · obtain ⟨result, s', hrun, _, _, hgood, hwin, _, _, _, hlive, _⟩ :=
      uw_post_public (copy := copy) (eo := off + copy.toNat) hg hw ha hro hasz hsrc (by omega) hfit hsep'
    have he : after = result := by rw [hr] at hrun; cases hrun; rfl
    have hgood' : Good after r zs z s' := by rw [he]; exact hgood
    have hs : state = s' := Option.some.inj (hstate.symm.trans hgood'.live.hs)
    have hwindow : state.window = .ref (.blk w) 0 := by rw [hs, hwin, hw]
    have howned : ∀ b, InflateOwned zs state b → h.live b := by
      intro b ho
      rcases ho with he | he
      · subst b; exact hzs
      · rw [hwindow] at he
        cases he
        simp [Heap.live, ha]
    intro b
    have hl : after.live b ↔ h.live b := by rw [he]; exact hlive b
    simp only [LiveChange, not_false_eq_true, and_true]
    constructor
    · intro he; exact Or.inl (hl.mp he)
    · intro he
      rcases he with he | ⟨ho, hn⟩
      · exact hl.mpr he
      · exact (hn (howned b ho)).elim

#print axioms uw_null_frame_public
#print axioms uw_null_mode_public
#print axioms updatewindow_mode_public
#print axioms updatewindow_frame_public
#print axioms updatewindow_live_public
end Zlib.Inflate.Proofs
