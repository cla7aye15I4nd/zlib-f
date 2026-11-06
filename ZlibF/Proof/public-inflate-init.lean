import ZlibF.Spec.Public.Domains
import ZlibF.Proof.«inflate.c.hdr»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec

namespace ZlibF.Spec.Public.Proofs.InflateInit

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


theorem init_ok_frame {h : Heap} {r : ZStreamRef} {z : ZStream} {wrap wb : Int32}
    (hz : r.get h = some z) (hF : Fresh h) :
    Frame h (initOkHeap h r z wrap wb) (StreamRoot r) := by
  unfold initOkHeap
  dsimp only
  rw [reset2Heap_null _ _ (initState r) (by rfl)]
  cases r with
  | tab k =>
    have hk : h.streams k = some z := hz
    simp only [Frame, allocIstHeap, setI, ZStreamRef.put, hk,
      upd_same, true_and]
    refine ⟨by omega, by omega, ?_⟩
    intro b hb hn
    have hne : b ≠ h.nextBlk := fun he => hF b (by omega) hb
    have hk : b ≠ k := fun he => hn (by simpa [StreamRoot] using he)
    simp [upd_ne, hne, hk]
  | in_gzstate_strm k =>
    cases hg : h.gzstates k with
    | none => simp [ZStreamRef.get, hg] at hz
    | some g =>
      simp only [Frame, allocIstHeap, setI, ZStreamRef.put, hg,
        upd_same, true_and]
      refine ⟨by omega, by omega, ?_⟩
      intro b hb hn
      have hne : b ≠ h.nextBlk := fun he => hF b (by omega) hb
      have hk : b ≠ k := fun he => hn (by simpa [StreamRoot] using he)
      simp [upd_ne, hne, hk]

#print axioms init_ok_frame

theorem init15_initial {h : Heap} {r : ZStreamRef} {z : ZStream} {v : BPtr}
    (hF : Fresh h) (hU : Uniq h) (hz : r.get h = some z)
    (ha : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc")
    (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : v ≠ .null) (hv0 : OkOn h (index8 v 0) 49) :
    InflateInitial h (initOkHeap h r z 5 15) r .zlib 15 := by
  obtain ⟨after, _, he, hg, ho⟩ :=
    inflateInit2_ok hU hF hz ha hza hzf hv hv0 (w := 15) params15
  subst after
  let z' := resetKeepStream (initStream2 z h.nextBlk) (resetPre (reset2Pre 5 15 (initState r)))
  let s' := resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r)))
  refine ⟨z', s', hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, init_ok_frame hz hF, ?_⟩
  all_goals try { rfl }
  all_goals try { rcases hza with e | e <;> rcases hzf with f | f <;>
    simp [z', resetKeepStream, resetPre, reset2Pre, initState, initStream2, initStream,
      InflateState.zeroed, InflateState.garbage, i2u, i2ul, e, f, HEAD] }
  intro b
  have hh := ho (fun b => h.live b) (fun _ => Iff.rfl) b
  simpa [LiveChange] using hh

#print axioms init15_initial

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`
The exact public result, state, frame and ownership contract. -/
theorem init15_public : Goal.inflateInit_ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h p version head size hv hbad
    cases head with
    | none =>
      rcases hv with ⟨rfl, _⟩ | ⟨b, hb, _⟩
      · exact inflateInit2_version_null p 15 size h
      · cases hb
    | some b =>
      obtain ⟨hn, hr⟩ := version_value_read hv
      by_cases hb : b = 49
      · subst b
        have hs : size ≠ 112 := by simpa using hbad
        exact inflateInit2_version_size p 15 version size h hn hr hs
      · exact inflateInit2_version_char p 15 version size h b hn hr hb
  · intro h version hv
    obtain ⟨hn, hr⟩ := version_value_read hv
    exact inflateInit2_nullstream 15 version h hn hr
  · intro h r z version hf hu _ hz ha hv
    obtain ⟨hn, hr⟩ := version_value_read hv
    obtain ⟨hza, hzf⟩ := ha
    by_cases hok : h.allocOk h.nalloc = true
    · refine ⟨Z_OK, initOkHeap h r z 5 15, ?_, ?_, ?_⟩
      · exact inflateInit2_success hz hf hok hza hzf hn hr params15
      · simp [initOkHeap, reset2Heap_null _ _ (initState r) (by rfl), allocIstHeap, setI]
      · have hnot : h.allocOk h.nalloc ≠ false := by rw [hok]; decide
        simp only [hnot]
        change True ∧ InflateInitial h (initOkHeap h r z 5 15) r .zlib 15
        exact ⟨trivial, init15_initial hf hu hz hok hza hzf hn hr⟩
    · have hfail : h.allocOk h.nalloc = false := by cases he : h.allocOk h.nalloc <;> simp_all
      refine ⟨Z_MEM_ERROR, initMemHeap h r z, ?_, ?_, ?_⟩
      · exact inflateInit2_memfail hz hf hok hza hzf hn hr
      · simp [initMemHeap]
      · simp only [hfail, ite_true]
        refine ⟨trivial, ?_⟩
        simp [SameObjects, initMemHeap, preparedStream, initStream]

#print axioms init15_public

theorem params_equiv (w : Int32) :
    reset2Params w = (Api.inflWbits w.toInt).map (fun (wr, n) =>
      ((match wr with | .raw => 0 | .zlib => 5 | .gzip => 6 | .auto => 7 : Int32), Int32.ofInt n)) := by
  by_cases hlo : w.toInt < -15
  · have hn : w < 0 := Int32.lt_iff_toInt_lt.mpr (by simpa using (show w.toInt < 0 by omega))
    have h15 : w < -15 := Int32.lt_iff_toInt_lt.mpr (by simpa using hlo)
    simp [reset2Params, hn, h15, Api.inflWbits, hlo, show w.toInt < 0 by omega]
  · by_cases hhi : 48 ≤ w.toInt
    · have hn : ¬ w < 0 := fun x => by have := Int32.lt_iff_toInt_lt.mp x; simp at this; omega
      have h48 : ¬ w < 48 := fun x => by have := Int32.lt_iff_toInt_lt.mp x; simp at this; omega
      have h16 : 15 < w := Int32.lt_iff_toInt_lt.mpr (by simpa using (show 15 < w.toInt by omega))
      have hb : badBits w = true := by simp [badBits, h16, show w ≠ 0 by intro h; subst w; simp at hhi]
      have hdiv0 : w.toInt / 16 ≠ 0 := by omega
      have hdiv1 : w.toInt / 16 ≠ 1 := by omega
      have hdiv2 : w.toInt / 16 ≠ 2 := by omega
      simp [reset2Params, hn, h48, hb, Api.inflWbits, show ¬ w.toInt < 0 by omega, hdiv0, hdiv1, hdiv2]
    · have hc : w.toInt = -15 ∨ w.toInt = -14 ∨ w.toInt = -13 ∨ w.toInt = -12 ∨
        w.toInt = -11 ∨ w.toInt = -10 ∨ w.toInt = -9 ∨ w.toInt = -8 ∨
        w.toInt = -7 ∨ w.toInt = -6 ∨ w.toInt = -5 ∨ w.toInt = -4 ∨
        w.toInt = -3 ∨ w.toInt = -2 ∨ w.toInt = -1 ∨ w.toInt = 0 ∨
        w.toInt = 1 ∨ w.toInt = 2 ∨ w.toInt = 3 ∨ w.toInt = 4 ∨
        w.toInt = 5 ∨ w.toInt = 6 ∨ w.toInt = 7 ∨ w.toInt = 8 ∨
        w.toInt = 9 ∨ w.toInt = 10 ∨ w.toInt = 11 ∨ w.toInt = 12 ∨
        w.toInt = 13 ∨ w.toInt = 14 ∨ w.toInt = 15 ∨ w.toInt = 16 ∨
        w.toInt = 17 ∨ w.toInt = 18 ∨ w.toInt = 19 ∨ w.toInt = 20 ∨
        w.toInt = 21 ∨ w.toInt = 22 ∨ w.toInt = 23 ∨ w.toInt = 24 ∨
        w.toInt = 25 ∨ w.toInt = 26 ∨ w.toInt = 27 ∨ w.toInt = 28 ∨
        w.toInt = 29 ∨ w.toInt = 30 ∨ w.toInt = 31 ∨ w.toInt = 32 ∨
        w.toInt = 33 ∨ w.toInt = 34 ∨ w.toInt = 35 ∨ w.toInt = 36 ∨
        w.toInt = 37 ∨ w.toInt = 38 ∨ w.toInt = 39 ∨ w.toInt = 40 ∨
        w.toInt = 41 ∨ w.toInt = 42 ∨ w.toInt = 43 ∨ w.toInt = 44 ∨
        w.toInt = 45 ∨ w.toInt = 46 ∨ w.toInt = 47 := by omega
      have hw : w = Int32.ofInt w.toInt := (Int32.ofInt_toInt w).symm
      rcases hc with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
        hcase | hcase | hcase | hcase | hcase | hcase | hcase
      all_goals rw [hcase] at hw; subst w; decide

#print axioms params_equiv

theorem api_bits_bound (w : Int) (wr : Api.Wrap) (n : Nat)
    (h : Api.inflWbits w = some (wr, n)) : n ≤ 15 := by
  unfold Api.inflWbits at h
  repeat' split at h
  all_goals simp_all <;> omega


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


def publicWrap : Api.Wrap → Int32
  | .raw => 0 | .zlib => 5 | .gzip => 6 | .auto => 7

theorem init_any_initial {h : Heap} {r : ZStreamRef} {z : ZStream} {v : BPtr} {w : Int32} {wr : Api.Wrap} {bits : Nat}
    (hF : Fresh h) (hU : Uniq h) (hz : r.get h = some z)
    (ha : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc")
    (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : v ≠ .null) (hv0 : OkOn h (index8 v 0) 49)
    (hp : Api.inflWbits w.toInt = some (wr, bits)) :
    InflateInitial h (initOkHeap h r z (publicWrap wr) (Int32.ofInt bits)) r wr bits := by
  have heq := params_equiv w
  rw [hp] at heq
  simp only [Option.map_some] at heq
  change reset2Params w = some (publicWrap wr, Int32.ofInt bits) at heq
  have hb := api_bits_bound w.toInt wr bits hp
  obtain ⟨after, _, he, hg, ho⟩ :=
    inflateInit2_ok hU hF hz ha hza hzf hv hv0 heq
  subst after
  let z' := resetKeepStream (initStream2 z h.nextBlk) (resetPre (reset2Pre (publicWrap wr) (Int32.ofInt bits) (initState r)))
  let s' := resetKeepState h.nextBlk (resetPre (reset2Pre (publicWrap wr) (Int32.ofInt bits) (initState r)))
  have hwindow : s'.window = .null := by
    simp [s', resetKeepState, resetPre, reset2Pre, initState]
  have hnat : (UInt32.ofNat bits).toNat = bits := by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨z', s', hg, ?_, ?_, ?_, hwindow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, init_ok_frame hz hF, ?_⟩
  all_goals try { rfl }
  all_goals try { rcases hza with e | e <;> rcases hzf with f | f <;>
    simp [z', resetKeepStream, resetPre, reset2Pre, initState, initStream2, initStream, e, f] }
  all_goals try {
    simp [s', resetKeepState, resetPre, reset2Pre, i2u]
    change (UInt32.ofNat bits).toNat = bits
    exact hnat }
  all_goals try { simp [s', resetKeepState, resetPre, reset2Pre] }
  intro b
  have hh := ho (fun b => h.live b) (fun _ => Iff.rfl) b
  simpa [LiveChange] using hh


#print axioms init_any_initial

theorem inflate_domain_general :
  ∀ h r version wb wrap bits,
    InitDomain h r version → Api.inflWbits wb.toInt = some (wrap, bits) →
    h.allocOk h.nalloc = true →
    ∃ after, C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ StreamReachable .inflate after r := by
  intro h r version wb wrap bits hd hp ha
  obtain ⟨hf, hu, hg, hv, z, hz, halloc, _⟩ := hd
  obtain ⟨hn, hv0⟩ := version_value_read hv
  have heq := params_equiv wb
  rw [hp] at heq
  change reset2Params wb = some (publicWrap wrap, Int32.ofInt bits) at heq
  let after := initOkHeap h r z (publicWrap wrap) (Int32.ofInt bits)
  have hr : C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) :=
    inflateInit2_success hz hf ha halloc.1 halloc.2 hn hv0 heq
  exact ⟨after, hr, init_any_initial hf hu hz ha halloc.1 halloc.2 hn hv0 hp,
    StreamReachable.inflateInit hf hu hg hz halloc hv hr⟩

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`
Initialization establishes the public representation domain. -/
theorem inflate_initialisation_domain_public : Goal.inflate_initialisation_domain := by
  refine ⟨inflate_domain_general, public_witness_domain, ?_⟩
  intro wb wrap bits hp
  obtain ⟨after, hr, hi, _⟩ := inflate_domain_general witnessHeap (.tab 0) (.ref (.blk 1) 0)
    wb wrap bits public_witness_domain hp (by rfl)
  exact ⟨after, hr, hi⟩

#print axioms inflate_initialisation_domain_public

end ZlibF.Spec.Public.Proofs.InflateInit
