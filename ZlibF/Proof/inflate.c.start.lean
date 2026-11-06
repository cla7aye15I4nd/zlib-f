import ZlibF.Proof.«inflate.c.end»

/-!
# inflate.c: `inflateInit2_` and `inflateInit_`
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem inflateReset2_ok_of {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) {w : Int32}
    {wrap wb : Int32} (hp : reset2Params w = some (wrap, wb)) :
    inflateReset2 (some r) w h = .ok (Z_OK, setI (r.put (reset2Heap h wb st)
        (resetKeepStream z (resetPre (reset2Pre wrap wb st)))) zs (resetKeepState zs (resetPre (reset2Pre wrap wb st)))) := by
  have := inflateReset2_run hL hf hwo w
  rw [hp] at this
  exact this.2

theorem inflateReset2_err_of {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) {w : Int32}
    (hp : reset2Params w = none) : inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h) := by
  have := inflateReset2_run hL hf hwo w
  rw [hp] at this
  exact this

@[simp] theorem allocIstHeap_streams (h : Heap) (st : InflateState) : (allocIstHeap h st).streams = h.streams := rfl
@[simp] theorem allocIstHeap_gzstates (h : Heap) (st : InflateState) : (allocIstHeap h st).gzstates = h.gzstates := rfl
@[simp] theorem allocIstHeap_bytes (h : Heap) (st : InflateState) : (allocIstHeap h st).bytes = h.bytes := rfl
@[simp] theorem allocIstHeap_ro (h : Heap) (st : InflateState) : (allocIstHeap h st).ro = h.ro := rfl
@[simp] theorem allocIstHeap_nextBlk (h : Heap) (st : InflateState) : (allocIstHeap h st).nextBlk = h.nextBlk + 1 := rfl
@[simp] theorem allocIstHeap_nalloc (h : Heap) (st : InflateState) : (allocIstHeap h st).nalloc = h.nalloc + 1 := rfl
@[simp] theorem allocIstHeap_istates_same (h : Heap) (st : InflateState) : (allocIstHeap h st).istates h.nextBlk = some st := by
  simp [allocIstHeap]
@[simp] theorem allocIstHeap_istates_ne (h : Heap) (st : InflateState) (x : Nat) (hx : x ≠ h.nextBlk) :
    (allocIstHeap h st).istates x = h.istates x := by simp [allocIstHeap, upd_ne _ _ _ _ hx]

@[simp] theorem ZStreamRef.get_allocIst (h : Heap) (st : InflateState) (r : ZStreamRef) :
    r.get (allocIstHeap h st) = r.get h := by cases r <;> rfl

@[simp] theorem ZStreamRef.put_allocIst (h : Heap) (st : InflateState) (r : ZStreamRef) (v : ZStream) :
    r.put (allocIstHeap h st) v = allocIstHeap (r.put h v) st := by
  cases r with
  | tab i => simp only [ZStreamRef.put, allocIstHeap]; cases hh : h.streams i <;> simp
  | in_gzstate_strm i => simp only [ZStreamRef.put, allocIstHeap]; cases hh : h.gzstates i <;> simp

@[simp] theorem allocIstHeap_istates_eq (h : Heap) (st : InflateState) (x : Nat) (hx : x = h.nextBlk) :
    (allocIstHeap h st).istates x = some st := by subst hx; simp

@[simp] theorem setI_allocIst (h : Heap) (g s : InflateState) (x : Nat) (hx : x = h.nextBlk) :
    setI (allocIstHeap h g) x s = allocIstHeap h s := by
  subst hx; simp [setI, allocIstHeap, upd_upd]

theorem zfrees_run' {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree")
    (zs : Nat) : ZFREES (some r) (some (.tab zs)) h = freeInflateState (some (.tab zs)) h := by
  simp [ZFREES, ldZ_eq, hz, hf]

theorem zfrees_run2 {h : Heap} {r : ZStreamRef} (hf : (r.get h).map (·.zfree) = some (.fn "zcfree")) (zs : Nat) :
    ZFREES (some r) (some (.tab zs)) h = freeInflateState (some (.tab zs)) h := by
  cases hz : r.get h with
  | none => simp [hz] at hf
  | some z =>
    simp [hz] at hf
    exact zfrees_run' hz hf zs

theorem freeI_eq (h : Heap) (zs : Nat) : freeInflateState (some (.tab zs)) h =
    match h.istates zs with
    | some _ => Except.ok ((), freeIst h zs)
    | none => Except.error (Fault.ub "free of a freed or invalid pointer (inflate_state)") := rfl

theorem zallocs_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hza : z.zalloc = .fn "zcalloc") :
    ZALLOCS (some r) h = allocInflateState h := by
  simp [ZALLOCS, ldZ_eq, hz, hza]

theorem allocIst_ok (h : Heap) (hok : h.allocOk h.nalloc = true) (hF : Fresh h) :
    allocInflateState h = .ok (some (.tab h.nextBlk), allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))) := by
  rw [allocInflateState_some hok hF.slotUsed_next]; rfl

theorem allocIst_put {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hok : h.allocOk h.nalloc = true)
    (hF : Fresh h) (v : ZStream) :
    allocInflateState (r.put h v) = .ok (some (.tab h.nextBlk),
      allocIstHeap (r.put h v) (InflateState.garbage (h.garbage h.nalloc))) := by
  have hF' : Fresh (r.put h v) := (shape_put hz v).fresh (by simp) hF
  rw [allocInflateState_some (by simpa using hok) hF'.slotUsed_next]
  simp [allocIstHeap]

theorem allocIst_fail_put {h : Heap} {r : ZStreamRef} (hok : ¬ h.allocOk h.nalloc = true) (v : ZStream) :
    allocInflateState (r.put h v) = .ok (none, { r.put h v with nalloc := h.nalloc + 1 }) := by
  have : ¬ (r.put h v).allocOk (r.put h v).nalloc = true := by simpa using hok
  rw [allocInflateState_none this]
  simp

theorem allocIst_fail (h : Heap) (hok : ¬ h.allocOk h.nalloc = true) :
    allocInflateState h = .ok (none, { h with nalloc := h.nalloc + 1 }) := allocInflateState_none hok

theorem fresh_allocIst {h : Heap} (hF : Fresh h) (st : InflateState) : Fresh (allocIstHeap h st) := by
  intro b hb hl
  simp only [allocIstHeap_nextBlk] at hb
  apply hF b (by omega)
  have hne : b ≠ h.nextBlk := by omega
  simpa only [Heap.live, allocIstHeap, upd_ne _ _ _ _ hne] using hl

theorem uniq_allocIst {h : Heap} (hU : Uniq h) (hF : Fresh h) (st : InflateState) : Uniq (allocIstHeap h st) := by
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb
    have := Heap.not_live.mp (hF _ (Nat.le_refl _))
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := this
    simp [allocIstHeap, e0, e1, e2, e3, e4, e6]
  · have := hU b
    simpa only [allocIstHeap, upd_ne _ _ _ _ hb] using this

theorem owns_allocIst {h : Heap} (hF : Fresh h) (st : InflateState) {S : Nat → Prop} (hO : h.Owns S) :
    (allocIstHeap h st).Owns (fun b => S b ∨ b = h.nextBlk) := by
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb; simp [Heap.live, allocIstHeap]
  · have := hO b
    simp only [Heap.live, allocIstHeap, upd_ne _ _ _ _ hb] at this ⊢
    simp [hb, this]

theorem inflateInit2_success {h : Heap} {r : ZStreamRef} {z : ZStream} {w : Int32} {version : BPtr}
    (hz : r.get h = some z) (hF : Fresh h) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49)
    {wrap wb : Int32} (hp : reset2Params w = some (wrap, wb)) :
    inflateInit2_ (some r) w version 112 h = .ok (Z_OK, initOkHeap h r z wrap wb) := by
  have hv0' : index8 version 0 h = .ok (49, h) := hv0
  unfold inflateInit2_
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
  isimp [hz, hv, hv0', initStream, hza, hzf, zallocs_run, allocIst_put hz hok hF]
  all_goals (
    rw [inflateReset2_ok_of (zs := h.nextBlk) (hp := hp)]
    rotate_left
    · exact ⟨by simp [hz]; rfl, allocIstHeap_istates_eq _ _ _ (by simp), by simp [StateRef.ofInflateState], by simp, by simp [HEAD, SYNC], by simp [initStream, hza], by simp [initStream, hza]⟩
    · simp
    · exact Or.inl rfl
    · simp [initOkHeap, initStream2, initState, initStream, hza, hzf, reset2Heap, freeWin_null, StateRef.ofInflateState])


theorem inflateInit2_version_null (strm : ZStreamPtr) (w : Int32) (sz : Int32) (h : Heap) :
    inflateInit2_ strm w .null sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateInit2_]

theorem inflateInit2_version_char (strm : ZStreamPtr) (w : Int32) (version : BPtr) (sz : Int32) (h : Heap) (c : UInt8)
    (hv : version ≠ .null) (hc : index8 version 0 h = .ok (c, h)) (hne : c ≠ 49) :
    inflateInit2_ strm w version sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateInit2_, hv, hc, hne]

theorem inflateInit2_version_size (strm : ZStreamPtr) (w : Int32) (version : BPtr) (sz : Int32) (h : Heap)
    (hv : version ≠ .null) (hc : index8 version 0 h = .ok (49, h)) (hne : sz ≠ 112) :
    inflateInit2_ strm w version sz h = .ok (Z_VERSION_ERROR, h) := by
  simp [inflateInit2_, hv, hc, hne]

theorem inflateInit2_nullstream (w : Int32) (version : BPtr) (h : Heap)
    (hv : version ≠ .null) (hc : index8 version 0 h = .ok (49, h)) :
    inflateInit2_ none w version 112 h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateInit2_, hv, hc]

theorem inflateInit2_memfail {h : Heap} {r : ZStreamRef} {z : ZStream} {w : Int32} {version : BPtr}
    (hz : r.get h = some z) (hF : Fresh h) (hok : ¬ h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49) :
    inflateInit2_ (some r) w version 112 h = .ok (Z_MEM_ERROR, initMemHeap h r z) := by
  have hv0' : index8 version 0 h = .ok (49, h) := hv0
  unfold inflateInit2_
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
  isimp [hz, hv, hv0', initStream, hza, hzf, zallocs_run, allocIst_fail_put (r := r) hok, initMemHeap, initStream]

theorem inflateInit2_badbits {h : Heap} {r : ZStreamRef} {z : ZStream} {w : Int32} {version : BPtr}
    (hz : r.get h = some z) (hF : Fresh h) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49)
    (hp : reset2Params w = none) :
    inflateInit2_ (some r) w version 112 h = .ok (Z_STREAM_ERROR, initBadHeap h r z) := by
  have hv0' : index8 version 0 h = .ok (49, h) := hv0
  unfold inflateInit2_
  rcases hza with hza | hza <;> rcases hzf with hzf | hzf <;>
  isimp [hz, hv, hv0', initStream, hza, hzf, zallocs_run, allocIst_put hz hok hF]
  all_goals (
    rw [inflateReset2_err_of (zs := h.nextBlk) (hp := hp)]
    rotate_left
    · exact ⟨by simp [hz]; rfl, allocIstHeap_istates_eq _ _ _ (by simp), by simp [StateRef.ofInflateState], by simp, by simp [HEAD, SYNC], by simp [initStream, hza], by simp [initStream, hza]⟩
    · simp
    · exact Or.inl rfl
    · isimp [initBadHeap, initStream2, initState, initStream, hza, hzf, reset2Heap, freeWin_null, StateRef.ofInflateState, zfrees_run2, freeI_eq, Z_STREAM_ERROR, Z_OK, hz])


theorem initState_win (r : ZStreamRef) (h : Heap) : WinInv h (initState r) := by
  refine ⟨?_, Or.inl rfl, fun _ => rfl, Or.inl rfl, ?_, ?_, ?_⟩
  all_goals simp [initState, InflateState.zeroed, InflateState.garbage, Junk.of]

theorem reset2Heap_null (h : Heap) (wb : Int32) (st : InflateState) (hw : st.window = .null) : reset2Heap h wb st = h := by
  unfold reset2Heap; split
  · rw [hw]; rfl
  · rfl

theorem wf_initState (r : ZStreamRef) : (initState r).WellFormed := by
  simp [initState, InflateState.WellFormed, InflateState.zeroed, InflateState.garbage]

theorem wf_reset2Pre (wrap wb : Int32) {st : InflateState} (hw : st.WellFormed) : (reset2Pre wrap wb st).WellFormed := by
  unfold InflateState.WellFormed at *
  unfold reset2Pre
  split <;> simpa using hw

theorem reset2Params_bits {w wrap wb : Int32} (hp : reset2Params w = some (wrap, wb)) : badBits wb = false := by
  unfold reset2Params at hp
  by_cases h1 : w < 0
  · by_cases h2 : w < -15
    · simp [h1, h2] at hp
    · have e : Int32.ofInt (-w.toInt) = -w := by simp
      simp only [h1, h2, ite_true, ite_false, e] at hp
      by_cases hb : badBits (-w) = true
      · simp [hb] at hp
      · simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        simpa using hb
  · by_cases h2 : w < 48
    · simp only [h1, h2, ite_true, ite_false] at hp
      by_cases hb : badBits (w &&& 15) = true
      · simp [hb] at hp
      · simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        simpa using hb
    · simp only [h1, h2, ite_true, ite_false] at hp
      by_cases hb : badBits w = true
      · simp [hb] at hp
      · simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        simpa using hb

/-- **inflateInit2_, success.** If the version arguments are right (`version[0]` is `'1'`, `stream_size` is 112), the
allocation of the state succeeds and `windowBits` is accepted (`reset2Params w = some (wrap, wb)`), the call returns
`Z_OK` without a fault. The new state is the block `h.nextBlk` (nothing else is allocated), the stream record has the
default allocator functions and points to it, the stream is initialised with the invariants intact, and the stream
owns exactly one more block (the state; the window is allocated later by `updatewindow`). The allocator functions
of the caller's record are `NULL` or the default ones (the model has no others). -/
theorem inflateInit2_ok {h : Heap} {r : ZStreamRef} {z : ZStream} {w : Int32} {version : BPtr}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z) (hok : h.allocOk h.nalloc = true)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version ≠ .null) (hv0 : OkOn h (index8 version 0) 49)
    {wrap wb : Int32} (hp : reset2Params w = some (wrap, wb)) :
    ∃ h', C.run (inflateInit2_ (some r) w version 112) h = .ok (Z_OK, h') ∧ h' = initOkHeap h r z wrap wb ∧
      Good h' r h.nextBlk (resetKeepStream (initStream2 z h.nextBlk)
        (resetPre (reset2Pre wrap wb (initState r)))) (resetKeepState h.nextBlk (resetPre (reset2Pre wrap wb (initState r)))) ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ b = h.nextBlk)) := by
  have hrun := inflateInit2_success hz hF hok hza hzf hv hv0 hp
  have hb : badBits wb = false := reset2Params_bits hp
  have hza' : (initStream z).zalloc ≠ .null := by
    rcases hza with hza | hza <;> simp [initStream, hza]
  have hzf' : (initStream z).zfree ≠ .null := by
    rcases hzf with hzf | hzf <;> simp [initStream, hzf]
  obtain ⟨z2, hz2⟩ : ∃ z2 : ZStream, z2 = initStream2 z h.nextBlk := ⟨_, rfl⟩
  have hzp : r.get (r.put h z2) = some z2 := by simp [hz]
  have hFp : Fresh (r.put h z2) := (shape_put hz z2).fresh (by simp) hF
  have hUp : Uniq (r.put h z2) := (shape_put hz z2).uniq hU
  have hFA := fresh_allocIst hFp (initState r)
  have hUA := uniq_allocIst hUp hFp (initState r)
  have e0 : reset2Heap (allocIstHeap (r.put h z2) (initState r)) wb (initState r) = allocIstHeap (r.put h z2) (initState r) :=
    reset2Heap_null _ _ _ rfl
  have hwin := winInv_reset2 (h := allocIstHeap (r.put h z2) (initState r)) (initState_win r _) (bits15 hb) wrap
  have hz0 : r.get (allocIstHeap (r.put h z2) (initState r)) = some z2 := by simp [hz]
  have hs0 : (allocIstHeap (r.put h z2) (initState r)).istates h.nextBlk = some (initState r) :=
    allocIstHeap_istates_eq _ _ _ (by simp)
  refine ⟨_, hrun, rfl, ?_, ?_⟩
  · unfold initOkHeap
    simp only [← hz2]
    rw [e0]
    refine good_set hz0 hs0 hUA hFA ?_ ?_ ?_ ?_ ?_ ?_
    · simp [resetKeepStream, hz2, initStream2]
    · simpa [resetKeepStream, hz2, initStream2] using hza'
    · simpa [resetKeepStream, hz2, initStream2] using hzf'
    · simp [resetKeepState, strm_pre, initState]
    · simpa [resetKeepState] using mode_head
    · rw [← e0]
      refine stInv_rk (wf_resetPre (wf_reset2Pre wrap wb (wf_initState r))) hwin ?_
      simpa [reqbits_resetPre, reset2Pre] using bits15 hb
  · intro S hO
    have h1 := owns_allocIst hFp (initState r) ((shape_put hz z2).owns hO)
    simp only [ZStreamRef.put_nextBlk] at h1
    unfold initOkHeap
    simp only [← hz2]
    rw [e0]
    exact ((shape_put hz0 _).trans (shape_setI (by simp only [ZStreamRef.put_istates]; exact hs0) _)).owns h1


theorem Shape.fresh_le {h h' : Heap} (hS : Shape h h') (hn : h.nextBlk ≤ h'.nextBlk) (hF : Fresh h) : Fresh h' := by
  intro b hb hl
  exact hF b (by omega) ((hS.live b).1 hl)

theorem shape_allocfree {H : Heap} (hF : Fresh H) (st : InflateState) :
    Shape H (freeIst (allocIstHeap H st) H.nextBlk) := by
  intro b
  by_cases hb : b = H.nextBlk
  · subst hb
    have := Heap.not_live.mp (hF _ (Nat.le_refl _))
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := this
    simp [freeIst, allocIstHeap, e0, e1, e2, e3, e4, e5, e6]
  · simp [freeIst, allocIstHeap, upd_ne _ _ _ _ hb]

theorem initMem_good {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hU : Uniq h) (hF : Fresh h) :
    Uniq (initMemHeap h r z) ∧ Fresh (initMemHeap h r z) ∧ (∀ b, (initMemHeap h r z).live b ↔ h.live b) := by
  have hS : Shape h (initMemHeap h r z) := by
    have := shape_put hz (initStream z)
    intro b; exact this b
  exact ⟨hS.uniq hU, hS.fresh (by simp [initMemHeap]) hF, hS.live⟩

theorem initBad_good {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hU : Uniq h) (hF : Fresh h) :
    Uniq (initBadHeap h r z) ∧ Fresh (initBadHeap h r z) ∧ (∀ b, (initBadHeap h r z).live b ↔ h.live b) := by
  have hFp : Fresh (r.put h (initStream2 z h.nextBlk)) := (shape_put hz _).fresh (by simp) hF
  have hS1 := shape_allocfree hFp (initState r)
  have hS2 : Shape h (initBadHeap h r z) := by
    unfold initBadHeap
    simp only [ZStreamRef.put_nextBlk] at hS1
    exact ((shape_put hz _).trans hS1).trans (shape_put (z0 := initStream2 z h.nextBlk) (by simp [hz]) _)
  exact ⟨hS2.uniq hU, hS2.fresh_le (by simp [initBadHeap]) hF, hS2.live⟩

/-- **inflateInit2_, safety (every outcome).** For a stream record `z` whose allocator functions are `NULL` or the default
ones (`zlib.h`: the caller sets them before the call; the model has only the defaults), a `version` that is `NULL` or
points to a readable byte, any `stream_size` and any `windowBits`, the call never faults and keeps `Uniq` and `Fresh`.
The outcome is exactly one of: a version error (`version` `NULL`, first character not `'1'`, or `stream_size` not 112:
nothing changes); `Z_MEM_ERROR` (the allocation oracle says no: no block is allocated, none leaks); `Z_STREAM_ERROR`
(`windowBits` refused: the state was allocated and is freed again, the stream's state pointer is `NULL`, the live
blocks are the old ones); `Z_OK` (see `inflateInit2_ok`). -/
theorem inflateInit2_safe {h : Heap} {r : ZStreamRef} {z : ZStream} {w : Int32} {version : BPtr} {sz : Int32}
    (hU : Uniq h) (hF : Fresh h) (hz : r.get h = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") (hzf : z.zfree = .null ∨ z.zfree = .fn "zcfree")
    (hv : version = .null ∨ ∃ c, OkOn h (index8 version 0) c) :
    ∃ v h', C.run (inflateInit2_ (some r) w version sz) h = .ok (v, h') ∧ Uniq h' ∧ Fresh h' ∧
      ((v = Z_VERSION_ERROR ∧ h' = h ∧ (version = .null ∨ (∃ c, OkOn h (index8 version 0) c ∧ c ≠ 49) ∨ sz ≠ 112)) ∨
       (v = Z_MEM_ERROR ∧ ¬ h.allocOk h.nalloc = true ∧ h' = initMemHeap h r z ∧ (∀ b, h'.live b ↔ h.live b)) ∨
       (v = Z_STREAM_ERROR ∧ h.allocOk h.nalloc = true ∧ reset2Params w = none ∧ h' = initBadHeap h r z ∧
          (∀ b, h'.live b ↔ h.live b)) ∨
       (v = Z_OK ∧ sz = 112 ∧ h.allocOk h.nalloc = true ∧ ∃ wrap wb, reset2Params w = some (wrap, wb) ∧
          h' = initOkHeap h r z wrap wb)) := by
  by_cases hvn : version = .null
  · subst hvn
    exact ⟨_, _, by rw [C.run]; exact inflateInit2_version_null _ _ _ _, hU, hF, Or.inl ⟨rfl, rfl, Or.inl rfl⟩⟩
  have hvc : ∃ c, OkOn h (index8 version 0) c := hv.resolve_left hvn
  obtain ⟨c, hc⟩ := hvc
  by_cases hc49 : c = 49
  · subst hc49
    by_cases hsz : sz = 112
    · subst hsz
      by_cases hok : h.allocOk h.nalloc = true
      · cases hp : reset2Params w with
        | none =>
          obtain ⟨u1, f1, l1⟩ := initBad_good hz hU hF
          exact ⟨_, _, inflateInit2_badbits hz hF hok hza hzf hvn hc hp, u1, f1,
            Or.inr (Or.inr (Or.inl ⟨rfl, hok, rfl, rfl, l1⟩))⟩
        | some p =>
          obtain ⟨wrap, wb⟩ := p
          obtain ⟨h', hr, he, hG, hO⟩ := inflateInit2_ok hU hF hz hok hza hzf hvn hc hp
          refine ⟨_, _, hr, hG.uniq, hG.fresh, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hok, wrap, wb, rfl, he⟩))⟩
      · obtain ⟨u1, f1, l1⟩ := initMem_good hz hU hF
        exact ⟨_, _, inflateInit2_memfail hz hF hok hza hzf hvn hc, u1, f1, Or.inr (Or.inl ⟨rfl, hok, rfl, l1⟩)⟩
    · exact ⟨_, _, by rw [C.run]; exact inflateInit2_version_size _ _ _ _ _ hvn hc hsz, hU, hF,
        Or.inl ⟨rfl, rfl, Or.inr (Or.inr hsz)⟩⟩
  · exact ⟨_, _, by rw [C.run]; exact inflateInit2_version_char _ _ _ _ _ c hvn hc hc49, hU, hF,
      Or.inl ⟨rfl, rfl, Or.inr (Or.inl ⟨c, hc, hc49⟩)⟩⟩

end Zlib.Inflate.Proofs
