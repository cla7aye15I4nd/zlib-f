import ZlibF.Proof.«inflate.c.sync2»

/-!
# inflate.c: `inflateSync`, the whole call

The call makes the local array `buf[4]`, runs the search and frees `buf` before returning.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate _root_.Zlib.Inflate.Spec

theorem freeWin_bytes_ne (H : Heap) (p : BPtr) {b : Nat} (hp : ∀ w, p = .ref (.blk w) 0 → w ≠ b) :
    (freeWin H p).bytes b = H.bytes b ∧ (freeWin H p).ro b = H.ro b := by
  cases p with
  | null => exact ⟨rfl, rfl⟩
  | ref x o =>
    cases x with
    | blk w =>
      cases o with
      | zero => have := hp w rfl; simp [freeWin, upd_ne _ _ _ _ (Ne.symm this)]
      | succ o => exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

theorem syncIn_syncAlloc {h : Heap} (hF : Fresh h) {p : BPtr} {len : UInt32} {bs : List UInt8}
    (I : SyncIn h p len bs) : SyncIn (syncAlloc h) p len bs := by
  rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | h2
  · have hb : b ≠ h.nextBlk := by
      intro e; subst e
      obtain ⟨e0, -⟩ := fresh_dead hF (Nat.le_refl _)
      rw [hg] at e0; cases e0
    exact Or.inl ⟨b, a, o, rfl, by rw [syncAlloc_bytes_ne h hb]; exact hg, hl, rfl⟩
  · exact Or.inr h2

theorem win_ne_buf {h : Heap} {st : InflateState} (hF : Fresh h) (hW : WinInv h st) :
    ∀ w, st.window = .ref (.blk w) 0 → w ≠ h.nextBlk := by
  intro w hw e
  subst e
  rcases hW.block with hn | ⟨w', a, hw', ha, -⟩
  · rw [hn] at hw; cases hw
  · rw [hw] at hw'
    have := (BRef.blk.inj (Ptr.ref.inj hw').1)
    subst this
    obtain ⟨e0, -⟩ := fresh_dead hF (Nat.le_refl _)
    rw [ha] at e0; cases e0

theorem syncOkHeap_bytes_ne (H : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) {b : Nat}
    (hb : ∀ w, s.window = .ref (.blk w) 0 → w ≠ b) :
    (syncOkHeap H r zs z s).bytes b = H.bytes b ∧ (syncOkHeap H r zs z s).ro b = H.ro b := by
  have hrp : ∀ w, (resetPre s).window = .ref (.blk w) 0 → w ≠ b := by
    intro w hw
    rw [resetPre_window] at hw
    split at hw
    · exact hb w hw
    · cases hw
  have hrh : (resetHeap H s).bytes b = H.bytes b ∧ (resetHeap H s).ro b = H.ro b := by
    unfold resetHeap; split
    · exact freeWin_bytes_ne H _ hb
    · exact ⟨rfl, rfl⟩
  unfold syncOkHeap
  split
  · have := freeWin_bytes_ne (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) (syncC zs s).window
      (by rw [(syncC_field zs s).2.1]; exact hrp)
    simpa [hrh.1, hrh.2] using this
  · simpa [hrh.1, hrh.2]

theorem good_freeBuf {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {nb : Nat}
    (hG : Good H r zs z st) (hn : ∀ w, st.window = .ref (.blk w) 0 → w ≠ nb) :
    Good (freeWin H (.ref (.blk nb) 0)) r zs z st := by
  obtain ⟨⟨hz, hs, zst, back, hm, za, zf⟩, ⟨wf, win, rq, bits, ptr⟩, hU, hF⟩ := hG
  refine ⟨⟨by simpa using hz, by simpa using hs, zst, back, hm, za, zf⟩, ⟨wf, ?_, rq, bits, ptr⟩,
    uniq_freeWin hU _, fresh_freeWin hF _⟩
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with h0 | ⟨w, a, hw, ha, hro, hsz⟩
  · exact Or.inl h0
  · have hne := hn w hw
    have := freeWin_bytes_ne H (.ref (.blk nb) 0) (b := w) (by intro w' e; have := BRef.blk.inj (Ptr.ref.inj e).1; subst this; exact Ne.symm hne)
    exact Or.inr ⟨w, a, hw, by rw [this.1]; exact ha, by rw [this.2]; exact hro, hsz⟩

theorem syncOkState_window_ref {zs : Nat} {s : InflateState} {w : Nat}
    (h : (syncOkState zs s).window = .ref (.blk w) 0) : s.window = .ref (.blk w) 0 := by
  by_cases h0 : s.reqbits = 0
  · rw [syncOkState_eq0 h0] at h; cases h
  · rw [syncOkState_ne0 h0, ] at h
    have h2 : (syncC zs s).window = .ref (.blk w) 0 := h
    rw [(syncC_field zs s).2.1, resetPre_window] at h2
    split at h2
    · assumption
    · cases h2

/-- **inflateSync, continuing a search** (`mode = SYNC` already, as after an earlier call that returned `Z_DATA_ERROR`).
The state's `have` is consistent with the bytes `w` searched so far (`SyncAt`); `zlib.h`: more input is given in
`next_in[0 .. avail_in)` (`SyncIn`) and there is input or a whole byte in the bit buffer. The call never faults. It
searches the input from `have` (`syncScan_spec` describes `N` and `G`) and consumes `N` bytes (`syncAdvance`). If the
pattern is not complete (`G ≠ 4`) it returns `Z_DATA_ERROR`, all input is consumed, only `have` changes in the state, and
the mode stays `SYNC`. If it is complete it returns `Z_OK` and the heap is `syncOkHeap` (the stream is reset but the
totals are kept, mode `TYPE`). The local array is made and freed (its block number is used up). Default `zfree` only. -/
theorem inflateSync_resume {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {bs w : List UInt8}
    (hG : Good h r zs z st) (hf : z.zfree = .fn "zcfree") (hmode : st.mode = SYNC)
    (hprog : ¬ (z.avail_in = 0 ∧ st.bits < 8)) (hI : SyncIn h z.next_in z.avail_in bs) (hA : SyncAt st.«have» w) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → syncPat <:+: w ++ bs.take N.toNat ∧ ∀ L', L' < N.toNat → ¬ syncPat <:+: w ++ bs.take L') ∧
      (G ≠ 4 → N = z.avail_in ∧ SyncSt G (w ++ bs)) ∧
      (G ≠ 4 → ∃ h', C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, h') ∧
        h' = freeWin (setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave st G)) (syncBuf h) ∧
        Good h' r zs (syncAdvance z N) (syncHave st G)) ∧
      (G = 4 → ∃ h', C.run (inflateSync (some r)) h = .ok (Z_OK, h') ∧
        h' = freeWin (syncOkHeap (setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave st G)) r zs (syncAdvance z N) (syncHave st G)) (syncBuf h) ∧
        Good h' r zs (syncOkStream (syncAdvance z N) (syncHave st G)) (syncOkState zs (syncHave st G))) := by
  have hF := hG.fresh
  have hG0 := good_syncAlloc hG
  have hI0 := syncIn_syncAlloc hF hI
  have hwn := win_ne_buf hF hG.inv.win
  obtain ⟨N, G, hN, h4, h3, hG1, hne, he⟩ := syncTail_run hG0 hf hI0 hA
  have hL0 := hG0.live
  have hbb : (syncAlloc h).bytes h.nextBlk = some (syncJunk h) := syncAlloc_bytes_buf h
  refine ⟨N, G, hN, h4, h3, fun hG4 => ?_, fun hG4 => ?_⟩
  · refine ⟨_, ?_, rfl, ?_⟩
    · show inflateSync (some r) h = _
      rw [inflateSync_split]
      isimp [allocLocalB_run h hF, stateCheck_live hL0, hL0.zst, hG.live.hz, hG.live.hs, hprog, hmode, hne hG4,
        freeBuf_run (H := setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave st G)) (nb := h.nextBlk) (a := syncJunk h)
          (by simpa using hbb) (by simp [syncAlloc_ro_buf]), syncBuf]
    · exact good_freeBuf (nb := h.nextBlk) hG1 (fun w hw => hwn w (by simpa [syncHave] using hw))
  · refine ⟨_, ?_, rfl, ?_⟩
    · have hbn : ∀ w', (syncHave st G).window = .ref (.blk w') 0 → w' ≠ h.nextBlk := fun w' hw' => hwn w' (by simpa [syncHave] using hw')
      have hby := syncOkHeap_bytes_ne (setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave st G)) r zs (syncAdvance z N) (syncHave st G) hbn
      show inflateSync (some r) h = _
      rw [inflateSync_split]
      isimp [allocLocalB_run h hF, stateCheck_live hL0, hL0.zst, hG.live.hz, hG.live.hs, hprog, hmode, he hG4,
        freeBuf_run (H := syncOkHeap (setI (r.put (syncAlloc h) (syncAdvance z N)) zs (syncHave st G)) r zs (syncAdvance z N) (syncHave st G))
          (nb := h.nextBlk) (a := syncJunk h) (by rw [hby.1]; simpa using hbb) (by rw [hby.2]; simp [syncAlloc_ro_buf]), syncBuf]
    · have hGd := (syncDone_good hG1).1
      exact good_freeBuf (nb := h.nextBlk) hGd (fun w hw => hwn w (by simpa [syncHave] using syncOkState_window_ref hw))

end Zlib.Inflate.Proofs
