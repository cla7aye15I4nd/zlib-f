import ZlibF.Proof.«inflate.c.window-compose»
import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«adler32.c.public-block»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public

/-- The public chronological window layout agrees with the mathematical ring
for every valid window index arrangement. -/
theorem ringList_public (a : Array UInt8) (ws wn wh : Nat)
    (hwn : wn ≤ wh) (hwh : wh ≤ ws) (hsize : ws ≤ a.size)
    (hcase : wh = ws ∨ wn = wh) :
    ringList a ws wn wh = (a.toList.drop wn).take (wh - wn) ++ a.toList.take wn := by
  have hlen1 : ((a.toList.drop wn).take (wh - wn)).length = wh - wn := by
    simp only [List.length_take, List.length_drop, Array.length_toList]
    apply Nat.min_eq_left
    omega
  have hlen2 : (a.toList.take wn).length = wn := by
    simp only [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (by omega)
  apply List.ext_getElem
  · simp [ringList, hlen1, hlen2]
    omega
  · intro i hi1 hi2
    have hi : i < wh := by simpa [ringList] using hi1
    simp only [ringList, List.getElem_map, List.getElem_range]
    by_cases hfirst : i < wh - wn
    · have hidx : wn + i < a.size := by omega
      simp only [List.getElem_append_left, hlen1, hfirst, List.getElem_take, List.getElem_drop]
      simp only [ringSlot]
      have hnot : ¬ wh ≤ wn := by omega
      have heq : ws - (wh - wn) = wn := by rcases hcase with h | h <;> omega
      simp [hnot, hfirst, heq, getElem!_pos a (wn + i) hidx, Array.getElem_toList]
    · have hsecond : i - (wh - wn) < wn := by omega
      have hidx : i - (wh - wn) < a.size := by omega
      simp only [List.getElem_append_right, hlen1, Nat.not_lt.mp hfirst, List.getElem_take]
      simp only [ringSlot]
      by_cases hle : wh ≤ wn
      · have heq : wn = wh := by omega
        simp [hle, heq, getElem!_pos a i (by omega), Array.getElem_toList]
      · simp [hle, hfirst, getElem!_pos a (i - (wh - wn)) hidx, Array.getElem_toList]

/-- The public dictionary predicate and ring contents describe the same bytes
for an existing window satisfying the stream invariant. -/
theorem inflateDictionary_eq_ring {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w : Nat} {a : Array UInt8} {xs : List UInt8}
    (hg : Good h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hasz : a.size = 2 ^ st.wbits.toNat) :
    InflateDictionary h st xs ↔ xs = ringList a st.wsize.toNat st.wnext.toNat st.whave.toNat := by
  have hws : st.wsize.toNat ≤ a.size := by
    have hs := hg.inv.win.ws
    rw [hasz]
    omega
  have hwh : st.whave.toNat ≤ st.wsize.toNat := hg.inv.win.hv
  have hwn : st.wnext.toNat ≤ st.whave.toNat := by
    by_cases ht : st.whave.toNat < st.wsize.toNat
    · have := hg.inv.win.eq ht; omega
    · have := hg.inv.win.wn; omega
  have hcase : st.whave.toNat = st.wsize.toNat ∨ st.wnext.toNat = st.whave.toNat := by
    by_cases ht : st.whave.toNat < st.wsize.toNat
    · exact Or.inr (hg.inv.win.eq ht)
    · left; omega
  have hsub : (st.whave - st.wnext).toNat = st.whave.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hwn)
  have hring := ringList_public a st.wsize.toNat st.wnext.toNat st.whave.toNat hwn hwh hws hcase
  constructor
  · intro hd
    rcases hd with ⟨hz, rfl⟩ | ⟨ref, off, data, hp, hget, _, hxs⟩
    · simp [ringList, hz]
    · rw [hw] at hp
      cases hp
      have he : data = a := Option.some.inj (hget.symm.trans (by simpa using ha))
      subst data
      simpa [hsub, hring] using hxs
  · intro hxs
    right
    refine ⟨.blk w, 0, a, hw, ?_, ?_, ?_⟩
    · simpa using ha
    · simpa using hws
    · simpa [hsub, hring] using hxs

theorem updatewindow_ring_public {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eo : Nat} {source : BRef}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hG : Good H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hasz : a.size = 2 ^ st.wbits.toNat)
    (heb : Space.get H source = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hsep : ZlibF.Spec.Public.Separate (.ref source (eo - copy.toNat)) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    ∃ H' st' A', updatewindow (some r) (.ref source eo) copy H = .ok (0, H') ∧ Good H' r zs z st' ∧
      H'.bytes w = some A' ∧
      ringList A' (initWinS st).wsize.toNat st'.wnext.toNat st'.whave.toNat =
        ((ringList a (initWinS st).wsize.toNat (initWinS st).wnext.toNat (initWinS st).whave.toNat ++
            newBytes ebytes eo copy.toNat).drop ((initWinS st).whave.toNat + copy.toNat - st'.whave.toNat)) ∧
      st'.whave.toNat = min (initWinS st).wsize.toNat ((initWinS st).whave.toNat + copy.toNat) := by
  have hI := hG.inv
  obtain ⟨f1, f2, f3, hv1, hwn1, heq1, -⟩ := initWinS_facts hI.win.wbits hI.win.ws hI.win.hv hI.win.wn hI.win.eq
  have hwb := hI.win.wbits
  have hle : (initWinS st).wsize.toNat ≤ 2 ^ 16 := by
    rw [f1]; have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : st.wbits.toNat ≤ 16); omega
  have hposn : (initWinS st).wsize.toNat ≠ 0 := by rw [f1]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  obtain ⟨H', st', hrun, hH', hst', hG', -, hb', -, -, -, -⟩ := uw_post_public hG hw ha hro hasz heb hc hoff hsep
  refine ⟨H', st', _, hrun, hG', hb', ?_, ?_⟩
  · rw [hst']
    exact ring_spec hposn hv1 hwn1 heq1 hle (by rw [f1]; omega) hc hoff (by rw [f1]; omega)
  · rw [hst']
    exact (uwPost_counts hposn hv1 hwn1 heq1 hle).1

/-- For an existing window, the actual update produces the exact public
dictionary suffix for every readable source and permitted separation. -/
theorem updatewindow_dictionary_existing {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {w off : Nat} {source : BRef} {a bytes : Array UInt8}
    {copy : UInt32} {old xs : List UInt8}
    (hg : Good h r zs z st) (hw : st.window = .ref (.blk w) 0)
    (ha : h.bytes w = some a) (hro : h.ro w = false) (hasz : a.size = 2 ^ st.wbits.toNat)
    (hsrc : Space.get h source = some bytes) (hfit : off + copy.toNat ≤ bytes.size)
    (hxs : xs = (bytes.toList.drop off).take copy.toNat) (hold : InflateDictionary h st old)
    (hsep : Separate (.ref source off) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    ∃ after state, updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) ∧
      Good after r zs z state ∧ state.window = st.window ∧
      InflateDictionary after state ((old ++ xs).drop ((old ++ xs).length - 2 ^ st.wbits.toNat)) := by
  let eo := off + copy.toNat
  have hc : copy.toNat ≤ eo := by dsimp [eo]; omega
  have hoff : eo ≤ bytes.size := hfit
  have hsep' : Separate (.ref source (eo - copy.toNat)) copy.toNat st.window (2 ^ st.wbits.toNat) := by
    simpa [eo] using hsep
  obtain ⟨after, state, hrun, _, hstate, hg', hwindow, hbytes, hsize, _, _, _⟩ :=
    uw_post_public hg hw ha hro hasz hsrc hc hoff hsep'
  refine ⟨after, state, hrun, hg', hwindow, ?_⟩
  have hwindow' : state.window = .ref (.blk w) 0 := hwindow.trans hw
  have hI := hg.inv.win
  obtain ⟨fsize, fbits, _, hv, hwn, heq, _⟩ :=
    initWinS_facts hI.wbits hI.ws hI.hv hI.wn hI.eq
  have hmax : (initWinS st).wsize.toNat ≤ 2 ^ 16 := by
    rw [fsize]
    have hwb := hI.wbits
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : st.wbits.toNat ≤ 16)
    omega
  have hpos : (initWinS st).wsize.toNat ≠ 0 := by rw [fsize]; exact Nat.ne_of_gt (Nat.two_pow_pos _)
  have hfields := uwPost_arith (st := initWinS st) (a := a) (ebytes := bytes) (eo := eo) (copy := copy)
    hpos hv hwn heq copy.toNat_lt hmax
  have hbits : state.wbits = st.wbits := by
    rw [hstate]
    exact hfields.2.1.trans fbits
  have hsize' : (uwPost (initWinS st) a bytes eo copy).1.size = 2 ^ state.wbits.toNat := by
    rw [hsize, hasz, hbits]
  apply (inflateDictionary_eq_ring hg' hwindow' hbytes hsize').2
  have hbefore := (inflateDictionary_eq_ring hg hw ha hasz).1 hold
  have hxs' : xs = newBytes bytes eo copy.toNat := by
    rw [hxs]
    have hh := Zlib.Adler32.Proofs.seg_eq_slice bytes off copy.toNat hfit
    simpa [Zlib.Adler32.Proofs.seg, newBytes, eo] using hh.symm
  have hinit : ringList a (initWinS st).wsize.toNat (initWinS st).wnext.toNat
      (initWinS st).whave.toNat = ringList a st.wsize.toNat st.wnext.toNat st.whave.toNat := by
    by_cases hz : st.wsize = 0
    · have hwh0 : st.whave.toNat = 0 := by have := hI.hv; rw [hz] at this; simpa using Nat.eq_zero_of_le_zero this
      simp [initWinS, hz, ringList, hwh0]
    · simp [initWinS, hz]
  have hwh : (initWinS st).whave.toNat = st.whave.toNat := by
    have hh := congrArg List.length hinit
    simpa only [ringList, List.length_map, List.length_range] using hh
  have hcount := (uwPost_counts (st := initWinS st) (a := a) (ebytes := bytes)
    (eo := eo) (copy := copy) hpos hv hwn heq hmax).1
  have hring := ring_spec (st := initWinS st) (a := a) (ebytes := bytes) (eo := eo) (copy := copy)
    hpos hv hwn heq hmax (by rw [fsize]; omega) hc hoff (by rw [fsize]; omega)
  rw [hstate, hfields.1, hring, hinit, ← hbefore, ← hxs']
  congr 1
  have holdlen : old.length = st.whave.toNat := by rw [hbefore]; simp [ringList]
  have hxslen : xs.length = copy.toNat := by rw [hxs']; simp [newBytes]
  rw [List.length_append, holdlen, hxslen, hcount, fsize, hwh]
  omega

/-- A newly allocated window retains the exact public dictionary suffix. -/
theorem updatewindow_dictionary_new {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {eo : Nat} {source : BRef} {ebytes : Array UInt8} {copy : UInt32}
    {old xs : List UInt8}
    (hG : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc") (hw : st.window = .null)
    (hok : h.allocOk h.nalloc = true) (heb : Space.get h source = some ebytes)
    (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hxs : xs = (ebytes.toList.drop (eo - copy.toNat)).take copy.toNat)
    (hold : InflateDictionary h st old) :
    ∃ H' st', updatewindow (some r) (.ref source eo) copy h = .ok (0, H') ∧
      Good H' r zs z st' ∧
      InflateDictionary H' st' ((old ++ xs).drop ((old ++ xs).length - 2 ^ st.wbits.toNat)) := by
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
  have hold0 : old = [] := by
    rcases hold with ⟨_, he⟩ | ⟨ref, off, a, he, _⟩
    · exact he
    · rw [hw] at he
      cases he
  have hwh0 : st.whave = 0 := by
    apply UInt32.toNat_inj.mp
    have hwh := hI.win.hv
    rw [hws0] at hwh
    simpa using Nat.eq_zero_of_le_zero hwh
  have hempty : InflateDictionary
      (setI (Zlib.Zutil.Proofs.allocHeap h ((1 <<< st.wbits : UInt32) * 1).toNat) zs (withWin st h.nextBlk))
      (withWin st h.nextBlk) [] := Or.inl ⟨by simpa [withWin] using hwh0, rfl⟩
  obtain ⟨H', st', hrun, hgood, _, hdict⟩ := updatewindow_dictionary_existing
    (hg := hG2) (w := h.nextBlk) (off := eo - copy.toNat) (source := source)
    (a := A0) (bytes := ebytes) (copy := copy) (old := []) (xs := xs)
    rfl (by simpa [setI] using hAb) (by simpa [setI] using hAro) hA0sz hbe
    (by omega) hxs hempty hsep
  refine ⟨H', st', ?_, hgood, ?_⟩
  · simpa [Nat.sub_add_cancel hc, withWin] using hrun
  · simpa [hold0, withWin] using hdict

/-- The complete `updatewindow` call preserves the stream invariant and either
retains the exact public dictionary suffix or reports a genuine allocation failure. -/
theorem updatewindow_dictionary_public {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {st : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    {old xs : List UInt8} (hg : Good h r zs z st) (hza : z.zalloc = .fn "zcalloc")
    (hsrc : Space.get h source = some bytes) (hfit : off + copy.toNat ≤ bytes.size)
    (hxs : xs = (bytes.toList.drop off).take copy.toNat) (hold : InflateDictionary h st old)
    (hsep : Separate (.ref source off) copy.toNat st.window (2 ^ st.wbits.toNat)) :
    ∃ v after state, C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h =
        .ok (v, after) ∧ Good after r zs z state ∧
      ((v = 0 ∧ InflateDictionary after state ((old ++ xs).drop ((old ++ xs).length - 2 ^ st.wbits.toNat))) ∨
       (v = 1 ∧ st.window = .null ∧ h.allocOk h.nalloc = false ∧
         after = setI { h with nalloc := h.nalloc + 1 } zs st ∧ state = st)) := by
  rcases hg.inv.win.block with hw | ⟨w, a, hw, ha, hro, hasz⟩
  · by_cases hok : h.allocOk h.nalloc = true
    · obtain ⟨after, state, hr, hgood, hdict⟩ :=
        updatewindow_dictionary_new (eo := off + copy.toNat) (copy := copy)
          hg hza hw hok hsrc (by omega) hfit (by simpa using hxs) hold
      exact ⟨0, after, state, hr, hgood, Or.inl ⟨rfl, hdict⟩⟩
    · have hfalse : h.allocOk h.nalloc = false := by cases he : h.allocOk h.nalloc <;> simp_all
      have hr := uw_alloc_fail hg.live hza hg.inv.win.wbits hw hok (.ref source (off + copy.toNat)) copy
      have hgood : Good (setI { h with nalloc := h.nalloc + 1 } zs st) r zs z st := by
        have hz' : r.get { h with nalloc := h.nalloc + 1 } = some z := by
          cases r <;> simpa [ZStreamRef.get] using hg.live.hz
        have he := good_set (h0 := { h with nalloc := h.nalloc + 1 }) (z0 := z) (z' := z)
          (s0 := st) (st' := st) hg.live.hz hg.live.hs hg.uniq hg.fresh hg.live.zst
          hg.live.zalloc hg.live.zfree hg.live.back hg.live.mode (StInv.congr (h := h) rfl rfl hg.inv)
        rwa [ZStreamRef.put_self hz'] at he
      exact ⟨1, _, st, hr, hgood, Or.inr ⟨rfl, hw, hfalse, rfl, rfl⟩⟩
  · obtain ⟨after, state, hr, hgood, _, hdict⟩ :=
      updatewindow_dictionary_existing hg hw ha hro hasz hsrc hfit hxs hold hsep
    exact ⟨0, after, state, hr, hgood, Or.inl ⟨rfl, hdict⟩⟩

#print axioms updatewindow_dictionary_public
#print axioms updatewindow_dictionary_new
#print axioms updatewindow_ring_public
#print axioms ringList_public
#print axioms inflateDictionary_eq_ring
#print axioms updatewindow_dictionary_existing
end Zlib.Inflate.Proofs
