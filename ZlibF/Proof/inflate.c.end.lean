import ZlibF.Proof.«inflate.c.init»

/-!
# inflate.c: `inflateEnd`, `inflateInit2_`, `inflateInit_`
-/

namespace Zlib.Inflate.Spec
open C

/-- The heap after `free(state)`: the state record is gone. -/
def freeIst (h : Heap) (zs : Nat) : Heap := { h with istates := upd h.istates zs none }

/-- The heap after `inflateEnd`'s two frees: the window block (if any), then the state record. -/
def endHeap (h : Heap) (zs : Nat) (st : InflateState) : Heap := freeIst (freeWin h st.window) zs

/-- The heap after a successful `ZALLOC` of an inflate state whose content is then set to `st`: the next block number
holds the record, the counters move. -/
def allocIstHeap (h : Heap) (st : InflateState) : Heap :=
  { h with istates := upd h.istates h.nextBlk (some st), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }

/-- The stream record after the first lines of `inflateInit2_`: no message, and the default allocator functions where
the caller gave none (`opaque` is cleared with the default `zalloc`). -/
def initStream (z : ZStream) : ZStream :=
  { z with
    msg := .null,
    zalloc := if z.zalloc == .null then .fn "zcalloc" else z.zalloc,
    «opaque» := if z.zalloc == .null then .null else z.opaque,
    zfree := if z.zfree == .null then .fn "zcfree" else z.zfree }

/-- The state record of `inflateInit2_` right after `zmemzero` and the three assignments, before `inflateReset2`. -/
def initState (r : ZStreamRef) : InflateState :=
  { InflateState.zeroed with strm := some r, window := .null, mode := HEAD }

/-- The stream record once its state pointer is set to the new state `nb`. -/
def initStream2 (z : ZStream) (nb : Nat) : ZStream := { initStream z with state := some (.inflate nb) }

/-- The heap after a successful `inflateInit2_` (`wrap` and `wb` from `reset2Params`): the state record is the block
`h.nextBlk`, built by `reset2Pre`/`inflateReset`; the stream record has the default allocator functions, a message of
`NULL`, and points to the state. -/
def initOkHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (wrap wb : Int32) : Heap :=
  let z2 : ZStream := initStream2 z h.nextBlk
  let H := allocIstHeap (r.put h z2) (initState r)
  let st0 := reset2Pre wrap wb (initState r)
  setI (r.put (reset2Heap H wb (initState r)) (resetKeepStream z2 (resetPre st0))) h.nextBlk
    (resetKeepState h.nextBlk (resetPre st0))

/-- The heap after `inflateInit2_` found the window bits invalid: the new state was allocated and is freed again, the
stream's state pointer is `NULL`. -/
def initBadHeap (h : Heap) (r : ZStreamRef) (z : ZStream) : Heap :=
  let z2 : ZStream := initStream2 z h.nextBlk
  r.put (freeIst (allocIstHeap (r.put h z2) (initState r)) h.nextBlk) { z2 with state := none }

/-- The heap after the allocation of the state failed: the stream has its defaults, the allocation counter moved. -/
def initMemHeap (h : Heap) (r : ZStreamRef) (z : ZStream) : Heap :=
  { r.put h (initStream z) with nalloc := h.nalloc + 1 }

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

@[simp] theorem freeIst_streams (h : Heap) (zs : Nat) : (freeIst h zs).streams = h.streams := rfl
@[simp] theorem freeIst_gzstates (h : Heap) (zs : Nat) : (freeIst h zs).gzstates = h.gzstates := rfl
@[simp] theorem freeIst_bytes (h : Heap) (zs : Nat) : (freeIst h zs).bytes = h.bytes := rfl
@[simp] theorem freeIst_nextBlk (h : Heap) (zs : Nat) : (freeIst h zs).nextBlk = h.nextBlk := rfl
@[simp] theorem freeIst_ro (h : Heap) (zs : Nat) : (freeIst h zs).ro = h.ro := rfl

@[simp] theorem ZStreamRef.get_freeIst (h : Heap) (zs : Nat) (r : ZStreamRef) : r.get (freeIst h zs) = r.get h := by
  cases r <;> simp [ZStreamRef.get]

@[simp] theorem ZStreamRef.put_freeIst (h : Heap) (zs : Nat) (r : ZStreamRef) (v : ZStream) :
    r.put (freeIst h zs) v = freeIst (r.put h v) zs := by
  cases r <;> simp [ZStreamRef.put, freeIst] <;> split <;> rfl

theorem uniq_freeIst {h : Heap} (hU : Uniq h) (zs : Nat) : Uniq (freeIst h zs) := by
  intro b
  have := hU b
  by_cases hb : b = zs
  · subst hb; simp only [freeIst, upd_same, cnt_none]; omega
  · simpa only [freeIst, upd_ne _ _ _ _ hb] using this

theorem fresh_freeIst {h : Heap} (hF : Fresh h) (zs : Nat) : Fresh (freeIst h zs) := by
  intro b hb hl
  apply hF b (by simpa using hb)
  by_cases hbz : b = zs
  · subst hbz
    simp only [Heap.live, freeIst, upd_same] at hl
    rcases hl with hl | hl | hl | hl | hl | hl | hl
    · exact Or.inl hl
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr (Or.inl hl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))
    · exact absurd rfl hl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  · simpa only [Heap.live, freeIst, upd_ne _ _ _ _ hbz] using hl

theorem owns_freeIst {h : Heap} (hU : Uniq h) {zs : Nat} {s : InflateState} (hs : h.istates zs = some s) {S : Nat → Prop}
    (hO : h.Owns S) : (freeIst h zs).Owns (fun b => S b ∧ b ≠ zs) := by
  intro b
  by_cases hbz : b = zs
  · subst hbz
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := Uniq.istates_only hU hs
    simp [Heap.live, freeIst, e1, e2, e3, e4, e5, e6]
  · have := hO b
    simp only [Heap.live, freeIst, upd_ne _ _ _ _ hbz] at this ⊢
    simp [hbz, this]

theorem zfrees_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree")
    {zs : Nat} {s : InflateState} (hs : h.istates zs = some s) :
    ZFREES (some r) (some (.tab zs)) h = .ok ((), freeIst h zs) := by
  simp [ZFREES, ldZ_eq, hz, hf, freeInflateState_tab hs, freeIst]

/-- **inflateEnd, safety and ownership.** On an initialised stream with the default `zfree` the call returns `Z_OK`
without a fault. It frees exactly the window block (if there is one) and the state record, and sets the stream's
state pointer to `NULL`. Nothing is allocated. Afterwards the live blocks are the old ones except the state and the
window: if the stream owned them with the blocks `S` before, it owns `S` minus its own two after (no leak, no double
free), and the stream check now fails. -/
theorem inflateEnd_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (hf : z.zfree = .fn "zcfree") :
    ∃ h', C.run (inflateEnd (some r)) h = .ok (Z_OK, h') ∧
      h' = r.put (endHeap h zs st) { z with state := none } ∧
      Uniq h' ∧ Fresh h' ∧ r.get h' = some { z with state := none } ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ ¬ OwnedBy zs st b)) ∧
      inflateStateCheck (some r) h' = .ok (1, h') := by
  have hL := hG.live
  have hz := hL.hz
  have hs := hL.hs
  have hwo := windowBlock hG.inv.win
  have hU1 : Uniq (freeWin h st.window) := uniq_freeWin hG.uniq _
  have hs1 : (freeWin h st.window).istates zs = some st := by simpa using hs
  have hz1 : r.get (freeWin h st.window) = some z := by simpa using hz
  have hrun : inflateEnd (some r) h = .ok (Z_OK, r.put (endHeap h zs st) { z with state := none }) := by
    unfold inflateEnd
    rcases hwo with hn | ⟨b, a, hb, hba, hro⟩
    · isimp [stateCheck_live hL, hL.zst, hz, hs, hn, zfrees_run (z := z) (by simpa using hz) hf (by simpa using hs : h.istates zs = some st), endHeap, freeWin_null]
    · have hz2 : r.get (freeWin h (.ref (.blk b) 0)) = some z := by simpa using hz
      have hs2 : (freeWin h (.ref (.blk b) 0)).istates zs = some st := by simpa using hs
      have e : endHeap h zs st = freeIst (freeWin h (.ref (.blk b) 0)) zs := by simp [endHeap, hb]
      rw [e]
      isimp [stateCheck_live hL, hL.zst, hz, hs, hb, zfreeB_run (p := .ref (.blk b) 0) hz hf (Or.inr ⟨b, a, rfl, hba, hro⟩),
        zfrees_run hz2 hf hs2]
  have hpost : (r.put (endHeap h zs st) { z with state := none }).istates = (endHeap h zs st).istates := by simp
  refine ⟨_, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have : Uniq (endHeap h zs st) := uniq_freeIst hU1 zs
    exact (shape_put (by simp [endHeap, hz] : r.get (endHeap h zs st) = some z) _).uniq this
  · have : Fresh (endHeap h zs st) := fresh_freeIst (fresh_freeWin hG.fresh _) zs
    exact (shape_put (by simp [endHeap, hz] : r.get (endHeap h zs st) = some z) _).fresh (by simp [endHeap]) this
  · simp [endHeap, hz]
  · intro S hO
    have hO1 : (freeWin h st.window).Owns (fun b => S b ∧ ¬ WinBlk st b) := by
      rcases hwo with hn | ⟨b, a, hb, hba, hro⟩
      · rw [hn, freeWin_null]
        intro x; rw [hO x]; simp [WinBlk, hn]
      · rw [hb]
        have := owns_freeWin hG.uniq hba hO
        intro x
        rw [this x]
        constructor
        · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
          intro hh; unfold WinBlk at hh; rw [hb] at hh
          exact h2 (BRef.blk.inj (Ptr.ref.inj hh).1).symm
        · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
          intro hh; apply h2; unfold WinBlk; rw [hb, hh]
    have hO2 := owns_freeIst hU1 hs1 hO1
    have hO3 : (endHeap h zs st).Owns (fun b => S b ∧ ¬ OwnedBy zs st b) := by
      intro x
      rw [show endHeap h zs st = freeIst (freeWin h st.window) zs from rfl, hO2 x]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        rintro (e | ⟨w, hw, e⟩)
        · exact h3 e
        · subst e; exact h2 hw
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun hw => h2 (Or.inr ⟨x, hw, rfl⟩)⟩, fun e => h2 (Or.inl e)⟩
    exact (shape_put (by simp [endHeap, hz] : r.get (endHeap h zs st) = some z) _).owns hO3
  · have hget : r.get (r.put (endHeap h zs st) { z with state := none }) = some { z with state := none } := by
      simp [endHeap, hz]
    have hD : StreamDom (r.put (endHeap h zs st) { z with state := none }) (some r) :=
      Or.inr ⟨r, { z with state := none }, rfl, hget, Or.inr (Or.inr (Or.inl rfl))⟩
    have hN : ¬ Initialised (r.put (endHeap h zs st) { z with state := none }) (some r) := by
      rintro ⟨r', zs', z', st', hh, hLL⟩
      cases hh
      have h1 := hLL.hz
      rw [hget] at h1
      cases h1
      have := hLL.zst
      simp at this
    exact notInit_check hD hN


theorem stInv_rk {h : Heap} {zs : Nat} {st : InflateState} (hwf : st.WellFormed) (hw : WinInv h st)
    (hq : st.reqbits.toNat ≤ 15) : StInv h zs (resetKeepState zs st) :=
  ⟨wf_resetKeepState hwf, ⟨hw.wbits, hw.block, hw.nullws, hw.ws, hw.hv, hw.wn, hw.eq⟩, hq, by simp [resetKeepState],
    ⟨⟨0, by simp [resetKeepState], by omega⟩,
      Or.inl ⟨0, 0, by simp [resetKeepState], by simp [resetKeepState], by omega, by omega⟩⟩⟩

end Zlib.Inflate.Proofs
