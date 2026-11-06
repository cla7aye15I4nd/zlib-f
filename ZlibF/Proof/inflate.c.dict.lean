import ZlibF.Proof.«inflate.c.ring»
import ZlibF.Proof.«adler32.c»

/-!
# inflate.c: `inflateGetDictionary` and `inflateSetDictionary`
-/

namespace Zlib.Inflate.Spec
open C

/-- The caller's dictionary buffer after `inflateGetDictionary` copied the window: `whave` bytes at offset `off`,
oldest first, in two pieces (`window[wnext .. whave)`, then `window[0 .. wnext)`). -/
def getDictBytes (D win : Array UInt8) (off wn wh : Nat) : Array UInt8 :=
  copyRange (copyRange D win off wn (wh - wn)) win (off + wh - wn) 0 wn

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem inflateGetDictionary_copy {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {w db off : Nat} {a D : Array UInt8} {dl : Option UInt32}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro db = false)
    (hD : H.bytes db = some D) (hne : db ≠ w) (hpos : st.whave ≠ 0) (hv : st.wnext.toNat ≤ st.whave.toNat)
    (hwh : st.whave.toNat ≤ a.size) (hfit : off + st.whave.toNat ≤ D.size) :
    inflateGetDictionary (some r) (.ref (.blk db) off) dl H =
      .ok ((Z_OK, dl.map (fun _ => st.whave)),
        { H with bytes := upd H.bytes db (some (getDictBytes D a off st.wnext.toNat st.whave.toNat)) }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsub : (st.whave - st.wnext).toNat = st.whave.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hv)
  have hwn : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hwh0 : (st.whave != 0) = true := by simpa using hpos
  have hn0' : Ptr.add (Ptr.ref (BRef.blk w) 0) (st.wnext.toNat : Int) H = .ok (Ptr.ref (BRef.blk w) (0 + st.wnext.toNat), H) :=
    Ptr.add_nat_ok (a := a) (by simpa using ha) (by omega)
  have hcp1 := memcpyB_blk_ok (nb := db) (no := off) (pb := w) (po := 0 + st.wnext.toNat) (n := (st.whave - st.wnext).toNat)
    (h := H) hD ha hro hne (by omega) (by omega)
  simp only [Nat.zero_add] at hcp1 hn0'
  unfold inflateGetDictionary
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, stateCheck_live hL, bne_iff_ne, ne_eq, hpos,
    not_false_eq_true, hw, hn0', hcp1, not_true_eq_false, ite_false, ite_true]
  simp only [bind_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hw, hn0', hcp1, bne_iff_ne, ne_eq, hpos, not_false_eq_true,
    ite_true, Bool.and_eq_true, hwh0, Ptr.noConfusion]
  have hnn : ¬ (Ptr.ref (BRef.blk db) off : BPtr) = Ptr.null := by simp
  simp only [true_and, hnn, not_false_eq_true, ite_true, bind_app, hn0', hcp1]
  have hA1sz : (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat).size = D.size := size_copyRange ..
  have hb1 : ({ H with bytes := upd H.bytes db (some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)) } : Heap).bytes db
      = some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat) := by simp
  have hbw1 : ({ H with bytes := upd H.bytes db (some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)) } : Heap).bytes w
      = some a := by simp [upd_ne _ _ _ _ hne.symm, ha]
  have hd1 := Ptr.add_nat_ok (h := ({ H with bytes := upd H.bytes db (some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)) } : Heap))
    (r := BRef.blk db) (off := off) (n := st.whave.toNat) (a := copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)
    (by simpa using hb1) (by omega)
  have hd2 := Ptr.sub_nat_ok (h := ({ H with bytes := upd H.bytes db (some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)) } : Heap))
    (r := BRef.blk db) (off := off + st.whave.toNat) (n := st.wnext.toNat) (a := copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)
    (by simpa using hb1) (by omega) (by omega)
  have hcp2 := memcpyB_blk_ok (nb := db) (no := off + st.whave.toNat - st.wnext.toNat) (pb := w) (po := 0) (n := st.wnext.toNat)
    (h := ({ H with bytes := upd H.bytes db (some (copyRange D a off st.wnext.toNat (st.whave - st.wnext).toNat)) } : Heap))
    hb1 hbw1 (by simpa using hro) hne (by omega) (by omega)
  have hd1' : Ptr.add (Ptr.ref (BRef.blk db) off) (st.whave.toNat : Int) _ = _ := hd1
  have hd2' : Ptr.add (Ptr.ref (BRef.blk db) (off + st.whave.toNat)) (-(st.wnext.toNat : Int)) _ = _ := hd2
  simp only [hd1', hd2', hcp2]
  cases dl <;> simp [getDictBytes, upd_upd, hsub]
  done

theorem getDictBytes_ring (D a : Array UInt8) (off ws wn wh : Nat) (hv : wn ≤ wh) (hwh : wh ≤ ws) (hws : ws ≤ a.size)
    (hfit : off + wh ≤ D.size) (hcase : wh = ws ∨ wn = wh) (j : Nat) (hj : j < wh) :
    (getDictBytes D a off wn wh)[off + j]! = a[ringSlot ws wn wh j]! := by
  have hin : (copyRange D a off wn (wh - wn)).size = D.size := size_copyRange ..
  unfold getDictBytes ringSlot
  rw [copyRange_bang _ _ _ _ _ (by omega) (by omega) _ (by omega)]
  repeat' split
  all_goals (try (rw [copyRange_bang _ _ _ _ _ (by omega) (by omega) _ (by omega)]; repeat' split))
  all_goals first | rfl | (exfalso; omega) | (congr 1 <;> omega)

/-- **inflateGetDictionary, specification and safety.** On an initialised stream whose window (if any) is not the
caller's buffer, with a `dictionary` that is `NULL` or has room for `whave` bytes: the call returns `Z_OK`, never
faults, and stores `*dictLength = whave` when `dictLength` is given. When `dictionary` is not `NULL` and `whave` is not 0,
the `whave` bytes at `dictionary` are afterwards the window's history, oldest first (`ringList`), and the rest of the
buffer is unchanged. -/
theorem inflateGetDictionary_spec {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {db off w : Nat} {a D : Array UInt8} {dl : Option UInt32}
    (hG : Good H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro db = false)
    (hD : H.bytes db = some D) (hne : db ≠ w) (hfit : off + st.whave.toNat ≤ D.size) :
    ∃ H', C.run (inflateGetDictionary (some r) (.ref (.blk db) off) dl) H = .ok ((Z_OK, dl.map (fun _ => st.whave)), H') ∧
      (st.whave = 0 ∧ H' = H ∨
       (st.whave ≠ 0 ∧ H' = { H with bytes := upd H.bytes db (some (getDictBytes D a off st.wnext.toNat st.whave.toNat)) } ∧
        (List.range st.whave.toNat).map (fun j => (getDictBytes D a off st.wnext.toNat st.whave.toNat)[off + j]!) =
          ringList a st.wsize.toNat st.wnext.toNat st.whave.toNat)) := by
  have hL := hG.live
  have hI := hG.inv
  by_cases h0 : st.whave = 0
  · refine ⟨H, ?_, Or.inl ⟨h0, rfl⟩⟩
    show inflateGetDictionary (some r) (.ref (.blk db) off) dl H = _
    unfold inflateGetDictionary
    have hnn : ¬ (Ptr.ref (BRef.blk db) off : BPtr) = Ptr.null := by simp
    cases dl <;> simp [stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, h0, hnn]
  · have hwn_le : st.wnext.toNat ≤ st.whave.toNat := by
      rcases Nat.lt_or_ge st.whave.toNat st.wsize.toNat with h1 | h1
      · have := hI.win.eq h1; omega
      · have := hI.win.wn; have := hI.win.hv; omega
    have hasz : a.size = 2 ^ st.wbits.toNat := by
      rcases hI.win.block with hb | ⟨w', a', hw', ha', -, hsz'⟩
      · rw [hb] at hw; cases hw
      · rw [hw] at hw'; have := (BRef.blk.inj (Ptr.ref.inj hw').1); subst this; rw [ha] at ha'; cases ha'; exact hsz'
    have hwsz : st.wsize.toNat ≤ a.size := by
      rcases hI.win.ws with h1 | h1
      · omega
      · omega
    have hwh0 : st.whave.toNat ≤ a.size := by have := hI.win.hv; omega
    refine ⟨_, ?_, Or.inr ⟨h0, rfl, ?_⟩⟩
    · exact inflateGetDictionary_copy hL hw ha hro hD hne h0 hwn_le hwh0 hfit
    · apply List.ext_getElem
      · simp [ringList]
      · intro j h1 h2
        simp only [ringList, List.getElem_map, List.getElem_range] at h1 h2 ⊢
        have hcase : st.whave.toNat = st.wsize.toNat ∨ st.wnext.toNat = st.whave.toNat := by
          rcases Nat.lt_or_ge st.whave.toNat st.wsize.toNat with h1 | h1
          · right; exact hI.win.eq h1
          · left; have := hI.win.hv; omega
        simp only [List.length_map, List.length_range] at h1
        exact getDictBytes_ring D a off _ _ _ hwn_le hI.win.hv hwsz hfit hcase j h1

theorem mode_mem : HEAD ≤ MEM ∧ MEM ≤ SYNC := by decide

theorem adler32_dict {H : Heap} {db off : Nat} {D : Array UInt8} (hD : H.bytes db = some D) (L : UInt32)
    (hfit : off + L.toNat ≤ D.size) :
    ∃ r, Zlib.Adler32.adler32 1 (.ref (.blk db) off) L H = .ok (r, H) ∧ r.toNat = Zlib.Adler32.Spec.adler32 1 (Zlib.Adler32.Proofs.seg D off L.toNat) := by
  have hL : L.toUInt64 = L.toNat.toUInt64 := by
    apply UInt64.toNat_inj.mp; simp
  have := Zlib.Adler32.Proofs.adler32_z_correct H db D hD 1 off L.toNat hfit (by have := L.toNat_lt; omega) (by decide)
  obtain ⟨r, hr, hv⟩ := this
  refine ⟨r, ?_, by simpa using hv⟩
  unfold Zlib.Adler32.adler32
  rw [hL]; exact hr

theorem adler32_init (H : Heap) : Zlib.Adler32.adler32 0 .null 0 H = .ok (1, H) := by
  simp [Zlib.Adler32.adler32, Zlib.Adler32.adler32_z]

/-- **inflateSetDictionary, safety.** For a good stream with the default allocator and a `dictionary` that is a
readable byte block holding `dictLength` bytes at `off` (not the stream's window), a stream that is raw (`wrap = 0`) or
waiting for its dictionary (`mode = DICT`, with the dictionary's Adler-32 equal to the one in the stream), the call
never faults. It returns `Z_OK` with the dictionary appended to the window history and `havedict = 1`, or
`Z_MEM_ERROR` (the window could not be allocated) with `mode = MEM`. The stream stays good. -/
theorem inflateSetDictionary_safe {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {db off : Nat} {D : Array UInt8} {L : UInt32}
    (hG : Good H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hD : H.bytes db = some D) (hfit : off + L.toNat ≤ D.size)
    (hdisj : ∀ w, st.window = .ref (.blk w) 0 → db ≠ w) (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hadler : st.mode = DICT → Zlib.Adler32.Spec.adler32 1 (Zlib.Adler32.Proofs.seg D off L.toNat) = st.check.toNat) :
    ∃ v H' st', C.run (inflateSetDictionary (some r) (.ref (.blk db) off) L) H = .ok (v, H') ∧ Good H' r zs z st' ∧
      ((v = Z_OK ∧ st'.havedict = 1 ∧ st'.window ≠ .null ∧
          ∀ S, H.Owns S → H'.Owns (fun b => S b ∨ (st.window = .null ∧ b = H.nextBlk))) ∨
       (v = Z_MEM_ERROR ∧ st'.mode = MEM ∧ st.window = .null ∧ ¬ H.allocOk H.nalloc = true)) := by
  have hL := hG.live
  obtain ⟨v0, H1, st1, hr1, hG1, hcase⟩ := updatewindow_safe (copy := L) (eb := db) (eo := off + L.toNat) (ebytes := D)
    hG hza hD (by omega) hfit hdisj
  have hadd : OkOn H (Ptr.add (Ptr.ref (BRef.blk db) off) (L.toNat : Int)) (Ptr.ref (BRef.blk db) (off + L.toNat)) :=
    Ptr.add_nat_ok (a := D) (by simpa using hD) hfit
  have hadd' : Ptr.add (Ptr.ref (BRef.blk db) off) (L.toNat : Int) H = .ok (Ptr.ref (BRef.blk db) (off + L.toNat), H) := hadd
  have hnn : (Ptr.ref (BRef.blk db) off == (Ptr.null : BPtr)) = false := by simp
  have hr1' : updatewindow (some r) (Ptr.ref (BRef.blk db) (off + L.toNat)) L H = .ok (v0, H1) := hr1
  have hstate : H.istates zs = some st := hL.hs
  have hrun : inflateSetDictionary (some r) (.ref (.blk db) off) L H =
      (if v0 = 0 then .ok (Z_OK, setI H1 zs { st1 with havedict := 1 })
       else .ok (Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM })) := by
    have hs1 : H1.istates zs = some st1 := hG1.live.hs
    unfold inflateSetDictionary
    simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn, bne_self_eq_false,
      Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hm : st.mode = DICT
    · obtain ⟨ra, hra, hrv⟩ := adler32_dict hD L hfit
      have hck : ra = st.check := by
        apply UInt64.toNat_inj.mp; rw [hrv]; exact hadler hm
      have hmb : (st.mode == DICT) = true := by simpa using hm
      simp only [hmb, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', ite_true, Bool.false_eq_true, ite_false, Bool.and_false, hmb, hm, beq_self_eq_true]
      simp only [bind_app, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
    · have hw0 : st.wrap = 0 := by rcases hwrap with h | h; exact h; exact absurd h hm
      have hmb : (st.mode == DICT) = false := by simpa using hm
      simp only [hmb, hw0, hadd', hr1', bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, Bool.and_false]
      simp only [bind_app, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
  have hs1 : H1.istates zs = some st1 := hG1.live.hs
  by_cases hv0 : v0 = 0
  · rcases hcase with ⟨-, hw1, hO⟩ | ⟨h1, -⟩
    · refine ⟨Z_OK, setI H1 zs { st1 with havedict := 1 }, { st1 with havedict := 1 }, ?_, ?_, Or.inl ⟨rfl, rfl, hw1, ?_⟩⟩
      · rw [C.run, hrun, if_pos hv0]
      · exact good_state hG1 rfl hG1.live.mode (hG1.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG1.inv.bits rfl rfl rfl)
      · intro S hOw
        have := (shape_setI hs1 { st1 with havedict := 1 }).owns (hO S hOw)
        exact this
    · rw [hv0] at h1; exact absurd h1 (by decide)
  · rcases hcase with ⟨h1, -⟩ | ⟨-, hw0, hnok, -, hst⟩
    · exact absurd h1 hv0
    · refine ⟨Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM }, { st1 with mode := MEM }, ?_, ?_, Or.inr ⟨rfl, rfl, hw0, hnok⟩⟩
      · rw [C.run, hrun, if_neg hv0]
      · exact good_state hG1 rfl mode_mem (hG1.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG1.inv.bits rfl rfl rfl)


/-- **inflateSetDictionary, wrong state.** A stream that has a wrapper (`wrap ≠ 0`) and is not waiting for a dictionary
(`mode ≠ DICT`) is refused: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateSetDictionary_streamerr {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {db off : Nat} {L : UInt32} (hL : Live H r zs z st) (hw : st.wrap ≠ 0) (hm : st.mode ≠ DICT) :
    C.run (inflateSetDictionary (some r) (.ref (.blk db) off) L) H = .ok (Z_STREAM_ERROR, H) := by
  have hnn : (Ptr.ref (BRef.blk db) off == (Ptr.null : BPtr)) = false := by simp
  have hb : (st.wrap != 0 && st.mode != DICT) = true := by simp [hw, hm]
  show inflateSetDictionary (some r) (.ref (.blk db) off) L H = _
  unfold inflateSetDictionary
  simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ite_false, hb, ite_true]
  rfl

/-- **inflateSetDictionary, wrong dictionary.** A stream waiting for its dictionary (`mode = DICT`) refuses one whose
Adler-32 is not the stream's `check`: `Z_DATA_ERROR`, nothing changes. -/
theorem inflateSetDictionary_dataerr {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {db off : Nat} {D : Array UInt8} {L : UInt32} (hL : Live H r zs z st) (hD : H.bytes db = some D)
    (hfit : off + L.toNat ≤ D.size) (hm : st.mode = DICT)
    (hbad : Zlib.Adler32.Spec.adler32 1 (Zlib.Adler32.Proofs.seg D off L.toNat) ≠ st.check.toNat) :
    C.run (inflateSetDictionary (some r) (.ref (.blk db) off) L) H = .ok (Z_DATA_ERROR, H) := by
  have hnn : (Ptr.ref (BRef.blk db) off == (Ptr.null : BPtr)) = false := by simp
  obtain ⟨ra, hra, hrv⟩ := adler32_dict hD L hfit
  have hne : (ra != st.check) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro e; apply hbad; rw [← hrv, e]
  have hmb : (st.mode == DICT) = true := by simpa using hm
  show inflateSetDictionary (some r) (.ref (.blk db) off) L H = _
  unfold inflateSetDictionary
  simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ite_false, hm, beq_self_eq_true, Bool.and_false, ite_true]
  simp only [bind_app, adler32_init, hra, hne, ite_true]
  rfl

end Zlib.Inflate.Proofs
