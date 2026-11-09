import ZlibF.Proof.«inflate.c.window-public-mode»
import ZlibF.Proof.«inflate.c.leave-finalize»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Only the four window fields change during updatewindow. All pending
symbol, bit-buffer and decoder-table fields remain the original fields. -/
def WindowStateFrame (before after : InflateState) : Prop :=
  after = { before with window := after.window, wsize := after.wsize, whave := after.whave, wnext := after.wnext }

theorem WindowStateFrame.trans {first second third : InflateState}
    (a : WindowStateFrame first second) (b : WindowStateFrame second third) :
    WindowStateFrame first third := by
  unfold WindowStateFrame at *
  rw [b, a]

theorem uwPost_windowStateFrame (s : InflateState) (a b : Array UInt8) (eo : Nat) (n : UInt32) :
    WindowStateFrame s (uwPost (initWinS s) a b eo n).2 := by
  unfold WindowStateFrame uwPost initWinS
  repeat' split
  all_goals rfl

/-- A new-window allocation and actual copy retain the complete non-window state. -/
theorem uw_null_state_frame_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {eo : Nat} {source : BRef} {ebytes : Array UInt8} {copy : UInt32}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ after state, updatewindow (some r) (.ref source eo) copy h = .ok (0, after) ∧
      Good after r zs z state ∧ WindowStateFrame st state ∧
      Space.get after source = some ebytes ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) := by
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
    | str b => exact (C.LibcBorrow.str_view_stable (Or.inr rfl)).trans heb
    | st_dist_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | st_length_code => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
    | dstate_depth b => simpa [Space.get, Zlib.Zutil.Proofs.allocHeap, setI] using heb
  have hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat
      (withWin st h.nextBlk).window (2 ^ (withWin st h.nextBlk).wbits.toNat) := by
    simp [ZlibF.Spec.Public.Separate, withWin, hne]
  obtain ⟨after, state, hr, heapEq, hstate, hgood, _, _, _, _, _, _⟩ :=
    uw_post_public (hG := hG2) (w := h.nextBlk) (source := source) (eo := eo)
      (a := A0) (ebytes := ebytes) (copy := copy) rfl (by simpa [setI] using hAb)
      (by simpa [setI] using hAro) hA0sz hbe hc hoff hsep
  have frame : WindowStateFrame st state := by
    rw [hstate]
    exact WindowStateFrame.trans (by rfl) (uwPost_windowStateFrame _ _ _ _ _)
  refine ⟨after, state, hr, hgood, frame, ?_, ?_⟩
  · rw [heapEq]
    cases source with
    | blk b =>
      have ne : b ≠ h.nextBlk := fun eq => hne (by rw [eq])
      simpa [Space.get, setI, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ ne] using heb
    | str b => exact (C.LibcBorrow.str_view_stable (Or.inr rfl)).trans heb
    | st_dist_code => simpa [Space.get, setI, Zlib.Zutil.Proofs.allocHeap] using heb
    | st_length_code => simpa [Space.get, setI, Zlib.Zutil.Proofs.allocHeap] using heb
    | dstate_depth b => simpa [Space.get, setI, Zlib.Zutil.Proofs.allocHeap] using heb
  · intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        simp only [Space.get, hgood.live.hs, hL.hs, Option.map_some]
        rw [frame]
      · rw [heapEq]
        simp [Space.get, setI, Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ same]
    | st_lenfix => rw [heapEq]; rfl
    | st_distfix => rw [heapEq]; rfl


/-- The actual successful callee preserves the full non-window state. -/
theorem updatewindow_state_frame_public {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (fit : off + copy.toNat ≤ bytes.size)
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat))
    (run : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after))
    (stored : after.istates zs = some state) : WindowStateFrame s state := by
  change updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) at run
  have sep : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      s.window (2 ^ s.wbits.toNat) := by simpa using separate
  rcases good.inv.win.block with window | ⟨w, a, window, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · obtain ⟨result, state', execution, nextGood, frame, _, _⟩ :=
        uw_null_state_frame_public (copy := copy) (eo := off + copy.toNat)
          good allocator window alloc get (by omega) fit
      have heaps : after = result := by rw [run] at execution; cases execution; rfl
      subst result
      have states : state = state' := Option.some.inj (stored.symm.trans nextGood.live.hs)
      simpa only [states] using frame
    · have fail := uw_alloc_fail good.live allocator good.inv.win.wbits window alloc
        (.ref source (off + copy.toNat)) copy
      rw [run] at fail
      cases fail
  · obtain ⟨result, state', execution, _, value, nextGood, _, _, _, _, _, _⟩ :=
      uw_post_public (copy := copy) (eo := off + copy.toNat)
        good window array ro size get (by omega) fit sep
    have heaps : after = result := by rw [run] at execution; cases execution; rfl
    have nextGood' : Good after r zs z state' := by rw [heaps]; exact nextGood
    have states : state = state' := Option.some.inj (stored.symm.trans nextGood'.live.hs)
    rw [states, value]
    exact uwPost_windowStateFrame _ _ _ _ _

theorem WindowStateFrame.pending {s state : InflateState} (frame : WindowStateFrame s state)
    (pending : DataPendingInvariant s) : DataPendingInvariant state := by
  rw [frame]
  exact ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩

/-- An actual complete window update retains the produced source view and
all decoder tables, including the genuine allocation-failure outcome. The
source exclusion follows from the public caller range, not a new API premise. -/
theorem updatewindow_decoder_boundary {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {eo : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → source ≠ .blk w) :
    ∃ rc after state, updatewindow (some r) (.ref source eo) copy h = .ok (rc, after) ∧
      Good after r zs z state ∧ WindowStateFrame s state ∧ Space.get after source = some bytes ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) ∧
      (rc = 0 ∨ (rc = 1 ∧ s.window = .null ∧ state = s ∧
        after = setI { h with nalloc := h.nalloc + 1 } zs s)) := by
  have sep : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, window, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  rcases good.inv.win.block with window | ⟨w, a, window, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · obtain ⟨after, state, run, nextGood, frame, sourceView, codeViews⟩ :=
        uw_null_state_frame_public good allocator window alloc get count bound
      exact ⟨0, after, state, run, nextGood, frame, sourceView, codeViews, Or.inl rfl⟩
    · obtain ⟨rc, after, state, run, nextGood, outcome⟩ :=
        updatewindow_safe_public good allocator get count bound sep
      rcases outcome with success | failure
      · have fail := uw_alloc_fail good.live allocator good.inv.win.wbits window alloc (.ref source eo) copy
        change updatewindow (some r) (.ref source eo) copy h = .ok (rc, after) at run
        rw [run, success.1] at fail
        cases fail
      · obtain ⟨eqrc, _, _, heapEq, stateEq⟩ := failure
        subst rc
        subst after
        subst state
        have same : setI { h with nalloc := h.nalloc + 1 } zs s = { h with nalloc := h.nalloc + 1 } :=
          tcSetI_same good.live.hs
        refine ⟨1, _, s, run, nextGood, by rfl, ?_, ?_, Or.inr ⟨rfl, window, rfl, rfl⟩⟩
        · rw [same]
          cases source <;> exact get
        · intro ref
          rw [same]
          cases ref <;> rfl
  · obtain ⟨after, state, run, heapEq, value, nextGood, _, _, _, _, _, _⟩ :=
      uw_post_public good window array ro size get count bound sep
    have frame : WindowStateFrame s state := by rw [value]; exact uwPost_windowStateFrame _ _ _ _ _
    refine ⟨0, after, state, run, nextGood, frame, ?_, ?_, Or.inl rfl⟩
    · rw [heapEq]
      cases source with
      | blk b =>
        have ne : b ≠ w := fun eq => unowned w window (by rw [eq])
        simpa [Space.get, setI, upd_ne _ _ _ _ ne] using get
      | str b => exact get
      | st_dist_code => exact get
      | st_length_code => exact get
      | dstate_depth b => exact get
    · intro ref
      cases ref with
      | istate_codes i =>
        by_cases same : i = zs
        · subst i
          simp only [Space.get, nextGood.live.hs, good.live.hs, Option.map_some]
          rw [frame]
        · rw [heapEq]
          simp [Space.get, setI, upd_ne _ _ _ _ same]
      | st_lenfix => rw [heapEq]; rfl
      | st_distfix => rw [heapEq]; rfl

end Zlib.Inflate.Proofs
