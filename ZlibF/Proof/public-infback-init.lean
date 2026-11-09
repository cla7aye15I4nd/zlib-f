import ZlibF.Spec.Public.Domains
import ZlibF.Proof.«infback.c.end»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec Zlib.Infback.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.InflateBackInitProof

theorem version_value_read {h : Heap} {v : BPtr} {byte : UInt8} (hv : VersionValue h v (some byte)) :
    v ≠ .null ∧ OkOn h (index8 v 0) byte := by
  rcases hv with ⟨_,h⟩ | ⟨b, hb, hbytes⟩
  · cases h
  · cases hb
    rcases hbytes with ⟨_,hn,_⟩ | ⟨ref,off,a,rfl,hget,hfit,hlist⟩
    · cases hn
    · refine ⟨by simp, ?_⟩
      have ha : off < a.size := by omega
      have he : a[off]? = some byte := by
        have hh := congrArg (fun l : List UInt8 => l[0]?) hlist
        simpa [List.getElem?_take, List.getElem?_drop] using hh.symm
      have hbyte : a[off] = byte := by
        have := Array.getElem?_eq_getElem ha
        rw [this] at he
        exact Option.some.inj he
      have hr := Ptr.index_ok (h := h) (r := ref) (a := a) (off := off) (i := 0) hget (by omega)
      simpa [hbyte] using hr

theorem init_refusals :
    (∀ h p wb window version head size, VersionValue h version head →
      (head ≠ some 49 ∨ size ≠ 112) →
      C.run (inflateBackInit_ p wb window version size) h = .ok (Z_VERSION_ERROR, h)) ∧
    (∀ h p wb window version, VersionValue h version (some 49) →
      (p = none ∨ window = .null ∨ wb.toInt < 8 ∨ 15 < wb.toInt) →
      C.run (inflateBackInit_ p wb window version 112) h = .ok (Z_STREAM_ERROR, h)) := by
  constructor
  · intro h p wb window version head size hv hbad
    cases head with
    | none =>
      rcases hv with ⟨rfl,_⟩ | ⟨b,hb,_⟩
      · exact inflateBackInit__version_null p wb window size h
      · cases hb
    | some b =>
      obtain ⟨hn,hr⟩ := version_value_read hv
      by_cases hb : b = 49
      · subst b
        have hs : size ≠ 112 := by simpa using hbad
        exact inflateBackInit__version_size p wb window version size h hn hr hs
      · exact inflateBackInit__version_char p wb window version size h b hn hr hb
  · intro h p wb window version hv hbad
    obtain ⟨hn,hr⟩ := version_value_read hv
    have hbad' : p = none ∨ window = .null ∨ wb < 8 ∨ wb > 15 := by
      rcases hbad with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Int32.lt_iff_toInt_lt.mpr (by simpa using h))))
      · exact Or.inr (Or.inr (Or.inr (Int32.lt_iff_toInt_lt.mpr (by simpa using h))))
    exact inflateBackInit__stream_error p wb window version h hn hr hbad'

theorem back_init_success_valid {h : Heap} {r : ZStreamRef} {z : ZStream} {wb : Int32} {window : BPtr}
    (hF : Fresh h) (hU : Uniq h) (hglob : LibraryGlobals h) (hz : r.get h = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (h8 : ¬ wb < 8) (h15 : ¬ wb > 15) (hwin : window ≠ .null)
    (hw : Writable h window (2 ^ wb.toInt.toNat)) :
    BackValid (backOkHeap h r z window wb) r h.nextBlk
      (initStream2 z h.nextBlk) (backState (h.garbage h.nalloc) window wb) := by
  have hr := i2u_range h8 h15
  have hwb : (i2u wb).toNat = wb.toInt.toNat := by
    unfold i2u
    rw [Int32.toNat_toUInt32_of_le]
    · rfl
    · rw [Int32.le_iff_toInt_le]
      have hnot : ¬ wb.toInt < 8 := fun he => h8 (Int32.lt_iff_toInt_lt.mpr (by simpa using he))
      simp only [Int32.toInt_zero]
      omega
  have ⟨hu,hf⟩ := backOk_shape hz hF window wb hU
  refine ⟨?_,?_,?_,?_,?_,wf_backState _ _ _,?_,?_,?_,?_,?_,hf,hu,?_⟩
  · simp [backOkHeap, hz]
  · simp [backOkHeap]
  · simp [initStream2]
  · rcases hza with e | e <;> simp [initStream2, initStream, e]
  · rcases hzf with e | e <;> simp [initStream2, initStream, e]
  · simpa [backState, i2u] using hr.1
  · simpa [backState, i2u] using hr.2
  · simp only [backState]
    exact shl32_one hr.2
  · simpa [backState] using hwin
  · rcases hw with ⟨hn,_⟩ | ⟨ref,off,a,hptr,hget,hro,hfit⟩
    · exact (hwin hn).elim
    · right
      refine ⟨ref,off,a,hptr,?_,?_,?_⟩
      · cases ref <;> simp_all [Space.get, backOkHeap, allocIstHeap]
      · cases ref <;> simp_all [Space.ro, backOkHeap, allocIstHeap]
      · simpa [backState, shl32_one hr.2, hwb] using hfit
  · simpa [LibraryGlobals, backOkHeap, allocIstHeap] using hglob

#print axioms back_init_success_valid

theorem back_init_frame {h : Heap} {r : ZStreamRef} {z : ZStream} {window : BPtr} {wb : Int32}
    (hz : r.get h = some z) (hF : Fresh h) :
    Frame h (backOkHeap h r z window wb) (StreamRoot r) := by
  cases r with
  | tab k =>
    have hk : h.streams k = some z := hz
    simp only [Frame, backOkHeap, allocIstHeap, ZStreamRef.put, hk, upd_same, true_and]
    refine ⟨by omega, by omega, ?_⟩
    intro b hb hn
    have hne : b ≠ h.nextBlk := fun he => hF b (by omega) hb
    have hk : b ≠ k := fun he => hn (by simpa [StreamRoot] using he)
    simp [upd_ne, hne, hk]
  | in_gzstate_strm k =>
    cases hg : h.gzstates k with
    | none => simp [ZStreamRef.get, hg] at hz
    | some g =>
      simp only [Frame, backOkHeap, allocIstHeap, ZStreamRef.put, hg, upd_same, true_and]
      refine ⟨by omega, by omega, ?_⟩
      intro b hb hn
      have hne : b ≠ h.nextBlk := fun he => hF b (by omega) hb
      have hk : b ≠ k := fun he => hn (by simpa [StreamRoot] using he)
      simp [upd_ne, hne, hk]

theorem back_init_live {h : Heap} {r : ZStreamRef} {z : ZStream} {window : BPtr} {wb : Int32}
    (hz : r.get h = some z) (hF : Fresh h) :
    LiveChange h (backOkHeap h r z window wb) (fun b => b = h.nextBlk) (fun _ => False) := by
  have hFp : Fresh (r.put h (initStream z)) := (shape_put hz _).fresh (by simp) hF
  have hz0 : r.get (allocIstHeap (r.put h (initStream z)) (backState (h.garbage h.nalloc) window wb)) =
      some (initStream z) := by simp [hz]
  have ho : h.Owns (fun b => h.live b) := fun _ => Iff.rfl
  have h1 := owns_allocIst hFp (backState (h.garbage h.nalloc) window wb) ((shape_put hz _).owns ho)
  simp only [ZStreamRef.put_nextBlk] at h1
  have h2 := (shape_put hz0 (initStream2 z h.nextBlk)).owns h1
  intro b
  simpa [LiveChange, backOkHeap] using h2 b

/-- `int inflateBackInit_(z_streamp strm, int windowBits, unsigned char *window,
The exact public result, state, frame and ownership contract. -/
theorem back_init_public : Goal.inflateBackInit_ := by
  obtain ⟨hversion, hstream⟩ := init_refusals
  refine ⟨hversion, hstream, ?_⟩
  intro h r z wb window version hF hU hglob hz halloc hv hlo hhi hwin hwrite
  obtain ⟨hvn, hv0⟩ := version_value_read hv
  have h8 : ¬ wb < 8 := by
    intro hh
    have hh' := Int32.lt_iff_toInt_lt.mp hh
    simp at hh'
    omega
  have h15 : ¬ wb > 15 := by
    intro hh
    have hh' := Int32.lt_iff_toInt_lt.mp hh
    simp at hh'
    omega
  obtain ⟨hza, hzf⟩ := halloc
  by_cases hok : h.allocOk h.nalloc = true
  · refine ⟨Z_OK, backOkHeap h r z window wb, ?_, ?_, ?_⟩
    · exact inflateBackInit__success hz hF hok hza hzf hvn hv0 hwin h8 h15
    · simp [backOkHeap, allocIstHeap]
    · have hnot : h.allocOk h.nalloc ≠ false := by rw [hok]; decide
      simp only [hnot]
      refine ⟨trivial, ?_, back_init_frame hz hF, back_init_live hz hF⟩
      simpa [preparedStream, initStream2, initStream, backInitialState, backState, i2u] using
        (back_init_success_valid hF hU hglob hz hza hzf h8 h15 hwin hwrite)
  · have hfail : h.allocOk h.nalloc = false := by
      cases he : h.allocOk h.nalloc <;> simp_all
    refine ⟨Z_MEM_ERROR, initMemHeap h r z, ?_, ?_, ?_⟩
    · exact inflateBackInit__memfail hz hF hok hza hzf hvn hv0 hwin h8 h15
    · simp [initMemHeap]
    · simp only [hfail, ite_true]
      refine ⟨trivial, ?_⟩
      simp [SameObjects, initMemHeap, preparedStream, initStream]

#print axioms back_init_public


theorem public_witness_fresh : Fresh witnessHeap := by
  intro b hb hl
  have h1 : b ≠ 1 := by simp [witnessHeap] at hb; omega
  have h2 : b ≠ 2 := by simp [witnessHeap] at hb; omega
  have h0 : b ≠ 0 := by simp [witnessHeap] at hb; omega
  simp [Heap.live, witnessHeap, Heap.empty, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h0] at hl

theorem public_witness_uniq : Uniq witnessHeap := by
  intro b
  by_cases h1 : b = 1
  · subst h1; simp [witnessHeap, Heap.empty, cnt]
  by_cases h2 : b = 2
  · subst h2; simp [witnessHeap, Heap.empty, cnt]
  by_cases h0 : b = 0
  · subst h0; simp [witnessHeap, Heap.empty, cnt]
  simp [witnessHeap, Heap.empty, cnt, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h0]

theorem public_witness_domain : InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) := by
  refine ⟨public_witness_fresh, public_witness_uniq, ?_, ?_, default, ?_, ?_, ?_⟩
  · rfl
  · right
    refine ⟨49, rfl, ?_⟩
    right
    refine ⟨.blk 1, 0, #[49, 0], rfl, ?_, ?_, ?_⟩ <;> simp [witnessHeap, Space.get, Heap.empty]
  · simp [ZStreamRef.get, witnessHeap]
  · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rfl

theorem back_domain_general :
  ∀ h r version wb window,
    InitDomain h r version → 8 ≤ wb.toInt → wb.toInt ≤ 15 →
    window ≠ .null → Writable h window (2 ^ wb.toInt.toNat) → h.allocOk h.nalloc = true →
    ∃ after z s, C.run (inflateBackInit_ (some r) wb window version 112) h =
      .ok (Z_OK, after) ∧ BackValid after r h.nextBlk z s ∧ s.window = window ∧
      s.wbits = wb.toUInt32 ∧ Frame h after (StreamRoot r) ∧
      LiveChange h after (fun b => b = h.nextBlk) (fun _ => False) := by
  intro h r version wb window hd hlo hhi hn hw ha
  obtain ⟨hf, hu, hg, hv, z, hz, hd, _⟩ := hd
  obtain ⟨rc, after, hrun, _, hs⟩ := back_init_public.2.2 h r z wb window version hf hu hg hz hd hv hlo hhi hn hw
  simp only [ha, Bool.true_eq_false, ite_false] at hs
  obtain ⟨rfl, valid, frame, live⟩ := hs
  exact ⟨after, _, _, hrun, valid, rfl, rfl, frame, live⟩

#print axioms public_witness_domain
#print axioms back_domain_general

theorem public_witness_window {wb : Int32} (hhi : wb.toInt ≤ 15) :
    Writable witnessHeap (.ref (.blk 2) 0) (2 ^ wb.toInt.toNat) := by
  right
  refine ⟨.blk 2, 0, Array.replicate 32768 0, rfl, ?_, ?_, ?_⟩
  · simp [witnessHeap, Space.get, Heap.empty]
  · simp [witnessHeap, Space.ro, Heap.empty]
  · simp only [Nat.zero_add, Array.size_replicate]
    have he : wb.toInt.toNat ≤ 15 := Int.toNat_le.mpr (by omega)
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) he) (by decide)

/-- `int inflateBackInit_(z_streamp strm, int windowBits, unsigned char *window,
Initialization establishes the public representation domain. -/
theorem back_init_domain_public : Goal.inflate_back_initialisation_domain := by
  refine ⟨back_domain_general, public_witness_domain, ?_⟩
  intro wb hlo hhi
  obtain ⟨after, z, s, hr, hv, hw, _, _, _⟩ :=
    back_domain_general witnessHeap (.tab 0) (.ref (.blk 1) 0) wb (.ref (.blk 2) 0)
      public_witness_domain hlo hhi (by simp) (public_witness_window hhi) (by rfl)
  exact ⟨after, z, s, hr, hv, hw⟩

#print axioms back_init_domain_public


theorem back_immediate_end {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hv : BackValid h r i z s) :
    C.run (inflateBackEnd (some r)) h = .ok (Z_OK, backEndHeap h r z i) := by
  obtain ⟨hz, hs, hstate, _, hfree, _⟩ := hv
  show inflateBackEnd (some r) h = _
  unfold inflateBackEnd
  have hz0 : z.zfree ≠ .null := by rw [hfree]; intro c; cases c
  have hs0 : z.state ≠ none := by rw [hstate]; intro c; cases c
  isimp [hz, hs0, hz0, hstate, hfree, zfrees_run hz hfree hs, backEndHeap]

theorem back_end_window {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hv : BackValid h r i z s) :
    Writable (backEndHeap h r z i) s.window s.wsize.toNat := by
  have hw := hv.2.2.2.2.2.2.2.2.2.2.1
  rcases hw with ⟨hn, hl⟩ | ⟨ref, off, a, hp, hg, hr, hn⟩
  · exact Or.inl ⟨hn,hl⟩
  · right
    refine ⟨ref, off, a, hp, ?_, ?_, hn⟩
    · cases ref with
      | blk block => simpa [backEndHeap, freeIst, Space.get] using hg
      | dstate_depth block => simpa [backEndHeap, freeIst, Space.get] using hg
      | str _ | st_dist_code | st_length_code => simp [Space.ro] at hr
    · cases ref <;> simp_all [backEndHeap, freeIst, Space.ro]

#print axioms back_end_window

theorem back_init_then_end {h : Heap} {r : ZStreamRef} {version : BPtr}
    {wb : Int32} {window : BPtr}
    (hd : InitDomain h r version) (hlo : 8 ≤ wb.toInt) (hhi : wb.toInt ≤ 15)
    (hn : window ≠ .null) (hw : Writable h window (2 ^ wb.toInt.toNat))
    (ha : h.allocOk h.nalloc = true) :
    ∃ middle final z,
      C.run (inflateBackInit_ (some r) wb window version 112) h = .ok (Z_OK, middle) ∧
      C.run (inflateBackEnd (some r)) middle = .ok (Z_OK, final) ∧
      r.get final = some z ∧ z.state = none ∧
      Writable final window (2 ^ wb.toInt.toNat) ∧
      (∀ b, final.live b ↔ h.live b) := by
  obtain ⟨middle, z, s, hi, hv, hwin, hbits, _, hlive⟩ :=
    back_domain_general h r version wb window hd hlo hhi hn hw ha
  let final := backEndHeap middle r z h.nextBlk
  have hrun := back_immediate_end hv
  have hget : r.get final = some { z with state := none } := by
    have hz := hv.1
    simp [final, backEndHeap, hz]
  have hwrite := back_end_window hv
  have hnat : s.wsize.toNat = 2 ^ wb.toInt.toNat := by
    have hsize := hv.2.2.2.2.2.2.2.2.1
    rw [hbits] at hsize
    have hwb : wb.toUInt32.toNat = wb.toInt.toNat := by
      rw [Int32.toNat_toUInt32_of_le]
      · rfl
      · rw [Int32.le_iff_toInt_le]
        simp only [Int32.toInt_zero]
        omega
    simpa [hwb] using hsize
  refine ⟨middle, final, { z with state := none }, hi, hrun, hget, rfl, ?_, ?_⟩
  · simpa [final, hwin, hnat] using hwrite
  · have huniq := hv.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hs := hv.2.1
    have hz := hv.1
    have ho : middle.Owns (fun b => middle.live b) := fun _ => Iff.rfl
    have hf := owns_freeIst huniq hs ho
    have hz' : r.get (freeIst middle h.nextBlk) = some z := by simpa using hz
    have hend := (shape_put hz' {z with state := none}).owns hf
    intro b
    have hbefore : ¬ h.live h.nextBlk := (hd.1) _ (Nat.le_refl _)
    have hmid := hlive b
    have he := hend b
    simp only [not_false_eq_true, and_true] at hmid
    constructor
    · intro hh
      have hparts := he.mp hh
      rcases hmid.mp hparts.1 with old | new
      · exact old
      · exact (hparts.2 new).elim
    · intro hh
      apply he.mpr
      refine ⟨hmid.mpr (Or.inl hh), ?_⟩
      intro eq
      subst b
      exact hbefore hh

#print axioms back_init_then_end

end ZlibF.Spec.Public.InflateBackInitProof
