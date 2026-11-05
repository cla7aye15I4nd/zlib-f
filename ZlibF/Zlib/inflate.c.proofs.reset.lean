import ZlibF.Zlib.«inflate.c.proofs.base»

/-!
# inflate.c: `inflateReset`, `inflateReset2`, `inflatePrime`, `inflateValidate`, `inflateUndermine`, `inflateMark`,
`inflateCodesUsed`, `inflateSyncPoint`, `inflateGetHeader`

Safety and specification of the stream functions that change the state record (and, for the two reset functions,
free the window).
-/

namespace Zlib.Inflate.Spec
open C

/-- The state record after `inflateReset` has made its changes and before `inflateResetKeep` runs: a window of another
size than the requested one is dropped, the requested window size and wrapper become current, the window is empty. -/
def resetPre (st : InflateState) : InflateState :=
  { (if st.wbits != st.reqbits then { st with window := .null, wbits := st.reqbits } else st) with
    wrap := st.reqwrap, wsize := 0, whave := 0, wnext := 0 }

/-- The heap after the window of `st` was freed, if `inflateReset` frees it. -/
def resetHeap (h : Heap) (st : InflateState) : Heap := if st.wbits != st.reqbits then freeWin h st.window else h

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem windowBlock {h : Heap} {st : InflateState} (hW : WinInv h st) :
    st.window = .null ∨ ∃ b a, st.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
  rcases hW.block with hn | ⟨w, a, hw, ha, hro, -⟩
  · exact Or.inl hn
  · exact Or.inr ⟨w, a, hw, ha, hro⟩

theorem Good.defz {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) : z.zalloc ≠ .null := hG.live.zalloc

theorem live_mid {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (h0 : Heap) (hz : r.get h0 = some z) (hs : h0.istates zs = some st) : Live h0 r zs z st :=
  ⟨hz, hs, hL.zst, hL.back, hL.mode, hL.zalloc, hL.zfree⟩

/-- The window pointer is `NULL` or a writable byte block that exists. -/
def WindowOk (h : Heap) (p : BPtr) : Prop := p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false

theorem inflateReset_run {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : st.wbits = st.reqbits ∨ WindowOk h st.window) :
    inflateReset (some r) h = .ok (Z_OK, setI (r.put (resetHeap h st) (resetKeepStream z (resetPre st))) zs
      (resetKeepState zs (resetPre st))) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsn : (h.istates zs).isSome := by simp [hs]
  unfold inflateReset
  by_cases hne : st.wbits = st.reqbits
  · isimp [stateCheck_live hL, hL.zst, hz, hs, hne]
    rw [resetKeep_run]
    rotate_left
    · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
    · simp [resetHeap, resetPre, hne, resetKeepState, resetKeepStream]
  · by_cases hw : st.window = .null
    · isimp [stateCheck_live hL, hL.zst, hz, hs, hne, hw]
      rw [resetKeep_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · simp [resetHeap, resetPre, hne, hw, resetKeepState, resetKeepStream, freeWin_null]
    · obtain ⟨b, a, hb, hba, hro⟩ : ∃ b a, st.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
        rcases hwo with hh | hn | hb
        · exact absurd hh hne
        · exact absurd hn hw
        · exact hb
      isimp [stateCheck_live hL, hL.zst, hz, hs, hne, hw, zfreeB_run hz hf (Or.inr ⟨b, a, hb, hba, hro⟩)]
      rw [resetKeep_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · simp [resetHeap, resetPre, hne, hw, resetKeepState, resetKeepStream, freeWin_null]


/-- The invariants of a stream after both records are replaced, over any heap that has the two records. -/
theorem good_set {h0 : Heap} {r : ZStreamRef} {zs : Nat} {z0 z' : ZStream} {s0 st' : InflateState}
    (hz0 : r.get h0 = some z0) (hs0 : h0.istates zs = some s0) (hU : Uniq h0) (hF : Fresh h0)
    (zst : z'.state = some (.inflate zs)) (za : z'.zalloc ≠ .null) (zf : z'.zfree ≠ .null)
    (back : st'.strm = some r) (hm : HEAD ≤ st'.mode ∧ st'.mode ≤ SYNC) (hI : StInv h0 zs st') :
    Good (setI (r.put h0 z') zs st') r zs z' st' := by
  have hS : Shape h0 (setI (r.put h0 z') zs st') :=
    (shape_put hz0 z').trans (shape_setI (by simpa using hs0) st')
  refine ⟨⟨?_, by simp, zst, back, hm, za, zf⟩, StInv.congr (h := h0) (h' := setI (r.put h0 z') zs st') (by simp) (by simp) hI,
    hS.uniq hU, hS.fresh (by simp) hF⟩
  simp [hz0]

theorem wf_resetPre {st : InflateState} (hw : st.WellFormed) : (resetPre st).WellFormed := by
  unfold InflateState.WellFormed at *
  unfold resetPre
  split <;> simpa using hw

theorem wf_resetKeepState {zs : Nat} {st : InflateState} (hw : st.WellFormed) : (resetKeepState zs st).WellFormed := by
  unfold InflateState.WellFormed at *
  simpa [resetKeepState] using hw

theorem reqbits_resetPre (st : InflateState) : (resetPre st).reqbits = st.reqbits := by
  unfold resetPre; split <;> rfl

theorem ptr_resetPre {zs : Nat} {st : InflateState} (hp : PtrInv zs st) : PtrInv zs (resetPre st) := by
  unfold PtrInv at *; unfold resetPre; split <;> simpa using hp

theorem bits_resetPre {st : InflateState} (hb : st.bits.toNat ≤ 39) : (resetPre st).bits.toNat ≤ 39 := by
  unfold resetPre; split <;> simpa using hb

theorem winInv_reset {h : Heap} {st : InflateState} (hW : WinInv h st) (hq : st.reqbits.toNat ≤ 15) :
    WinInv (resetHeap h st) (resetPre st) := by
  by_cases hne : st.wbits = st.reqbits
  · have e : resetHeap h st = h := by simp [resetHeap, hne]
    rw [e]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [resetPre, hne] using hW.wbits
    · simpa [resetPre, hne] using hW.block
    · intro _; simp [resetPre, hne]
    · simp [resetPre, hne]
    · simp [resetPre, hne]
    · simp [resetPre, hne]
    · intro hh; simp [resetPre, hne] at hh
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [resetPre, hne] using hq
    · left; simp [resetPre, hne]
    · intro _; simp [resetPre, hne]
    · simp [resetPre, hne]
    · simp [resetPre, hne]
    · simp [resetPre, hne]
    · intro hh; simp [resetPre, hne] at hh

theorem resetHeap_owns {h : Heap} {st : InflateState} (hU : Uniq h) (hW : WinInv h st) {S : Nat → Prop}
    (hO : h.Owns S) : (resetHeap h st).Owns (fun b => S b ∧ ¬ (st.wbits ≠ st.reqbits ∧ WinBlk st b)) := by
  by_cases hne : st.wbits = st.reqbits
  · have e : resetHeap h st = h := by simp [resetHeap, hne]
    rw [e]
    intro b; rw [hO b]; simp [hne]
  · have e : resetHeap h st = freeWin h st.window := by simp [resetHeap, hne]
    rw [e]
    rcases windowBlock hW with hn | ⟨w, a, hw, hb, hro⟩
    · rw [hn, freeWin_null]
      intro b; rw [hO b]; simp [WinBlk, hn]
    · rw [hw]
      have := owns_freeWin hU hb hO
      intro b
      rw [this b]
      constructor
      · rintro ⟨hS, hbw⟩
        refine ⟨hS, ?_⟩
        rintro ⟨-, hwb⟩
        apply hbw
        unfold WinBlk at hwb
        rw [hw] at hwb
        exact (BRef.blk.inj (Ptr.ref.inj hwb).1).symm
      · rintro ⟨hS, hh⟩
        refine ⟨hS, fun hbw => hh ⟨hne, ?_⟩⟩
        unfold WinBlk
        rw [hw, hbw]

/-- **inflateReset, safety.** On an initialised stream with the default `zfree` the call returns `Z_OK` without a
fault. If the current window size is not the requested one, the window block is freed (the only free; nothing is
allocated). The records become `resetKeepStream`/`resetKeepState` of `resetPre st`; the stream is initialised again
and the invariants hold. -/
theorem inflateReset_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (hf : z.zfree = .fn "zcfree") :
    ∃ h', C.run (inflateReset (some r)) h = .ok (Z_OK, h') ∧
      h' = setI (r.put (resetHeap h st) (resetKeepStream z (resetPre st))) zs (resetKeepState zs (resetPre st)) ∧
      Good h' r zs (resetKeepStream z (resetPre st)) (resetKeepState zs (resetPre st)) ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ ¬ (st.wbits ≠ st.reqbits ∧ WinBlk st b))) := by
  have hL := hG.live
  have hU : Uniq (resetHeap h st) := by
    unfold resetHeap; split
    · exact uniq_freeWin hG.uniq _
    · exact hG.uniq
  have hF : Fresh (resetHeap h st) := by
    unfold resetHeap; split
    · exact fresh_freeWin hG.fresh _
    · exact hG.fresh
  have hz0 : r.get (resetHeap h st) = some z := by unfold resetHeap; split <;> simp [hL.hz]
  have hs0 : (resetHeap h st).istates zs = some st := by unfold resetHeap; split <;> simp [hL.hs]
  have hI : StInv (resetHeap h st) zs (resetKeepState zs (resetPre st)) := by
    have hw := winInv_reset hG.inv.win hG.inv.reqbits
    refine ⟨wf_resetKeepState (wf_resetPre hG.inv.wf), ?_, by simpa [resetKeepState, reqbits_resetPre] using hG.inv.reqbits, by simp [resetKeepState], ?_⟩
    · exact ⟨hw.wbits, hw.block, hw.nullws, hw.ws, hw.hv, hw.wn, hw.eq⟩
    · exact (StInv.resetKeep (st := resetPre st) ⟨wf_resetPre hG.inv.wf, hw, by simpa [reqbits_resetPre] using hG.inv.reqbits, bits_resetPre hG.inv.bits, ptr_resetPre hG.inv.ptr⟩).ptr
  refine ⟨_, inflateReset_run hG.live hf (Or.inr (windowBlock hG.inv.win)), rfl, ?_, ?_⟩
  · refine good_set hz0 hs0 hU hF (by simp [resetKeepStream, hL.zst]) (by simpa [resetKeepStream] using hL.zalloc)
      (by simpa [resetKeepStream] using hL.zfree) (by simp [resetKeepState, resetPre]; split <;> exact hL.back)
      (by simpa [resetKeepState] using mode_head) hI
  · intro S hO
    have hO' := resetHeap_owns hG.uniq hG.inv.win hO
    exact ((shape_put hz0 _).trans (shape_setI (by simpa using hs0) _)).owns hO'

end Zlib.Inflate.Proofs
