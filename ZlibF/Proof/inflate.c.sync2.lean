import ZlibF.Proof.«inflate.c.sync»
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Proof.«inflate.c.misc»

/-!
# inflate.c: `inflateSync`

Infrastructure: the local array `unsigned char buf[4]` is a block taken at the start of the call (`syncAlloc`) and
freed before every return (`freeWin ... buf`); the block number is never reused.
-/

namespace Zlib.Inflate.Spec
open C

/-- The initial (arbitrary) content of `buf[4]`. -/
def syncJunk (h : Heap) : Array UInt8 := Array.ofFn (n := 4) fun i => Junk.of (h.garbage h.nalloc i.val)

/-- The heap after the local array `buf[4]` is made: block `h.nextBlk`, writable. -/
def syncAlloc (h : Heap) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some (syncJunk h)), ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1 }

/-- The pointer to the local array. -/
def syncBuf (h : Heap) : BPtr := .ref (.blk h.nextBlk) 0

/-- The heap after a call that did nothing but make and free the local array. -/
def tmpFreed (h : Heap) : Heap := freeWin (syncAlloc h) (syncBuf h)

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem allocLocalB_run (h : Heap) (hF : Fresh h) : allocLocalB 4 h = .ok (syncBuf h, syncAlloc h) := by
  have hs := hF.slotUsed_next
  simp [allocLocalB, allocBytes, hs, syncBuf, syncAlloc, syncJunk]

@[simp] theorem syncAlloc_streams (h : Heap) : (syncAlloc h).streams = h.streams := rfl
@[simp] theorem syncAlloc_gzstates (h : Heap) : (syncAlloc h).gzstates = h.gzstates := rfl
@[simp] theorem syncAlloc_istates (h : Heap) : (syncAlloc h).istates = h.istates := rfl
@[simp] theorem syncAlloc_words (h : Heap) : (syncAlloc h).words = h.words := rfl
@[simp] theorem syncAlloc_gzheaders (h : Heap) : (syncAlloc h).gzheaders = h.gzheaders := rfl
@[simp] theorem syncAlloc_dstates (h : Heap) : (syncAlloc h).dstates = h.dstates := rfl
@[simp] theorem syncAlloc_nextBlk (h : Heap) : (syncAlloc h).nextBlk = h.nextBlk + 1 := rfl
@[simp] theorem syncAlloc_nalloc (h : Heap) : (syncAlloc h).nalloc = h.nalloc := rfl
@[simp] theorem syncAlloc_allocOk (h : Heap) : (syncAlloc h).allocOk = h.allocOk := rfl
@[simp] theorem syncAlloc_garbage (h : Heap) : (syncAlloc h).garbage = h.garbage := rfl
@[simp] theorem syncAlloc_static (h : Heap) : (syncAlloc h).static = h.static := rfl

@[simp] theorem ZStreamRef.get_syncAlloc (h : Heap) (r : ZStreamRef) : r.get (syncAlloc h) = r.get h := by
  cases r <;> rfl

theorem syncAlloc_bytes_buf (h : Heap) : (syncAlloc h).bytes h.nextBlk = some (syncJunk h) := by
  simp [syncAlloc]
theorem syncAlloc_ro_buf (h : Heap) : (syncAlloc h).ro h.nextBlk = false := by
  simp [syncAlloc]
theorem syncAlloc_bytes_ne (h : Heap) {b : Nat} (hb : b ≠ h.nextBlk) : (syncAlloc h).bytes b = h.bytes b := by
  simp [syncAlloc, upd_ne _ _ _ _ hb]

theorem fresh_dead {h : Heap} (hF : Fresh h) {b : Nat} (hb : h.nextBlk ≤ b) :
    h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧
    h.istates b = none ∧ h.gzstates b = none :=
  Heap.not_live.mp (hF b hb)

theorem uniq_syncAlloc {h : Heap} (hU : Uniq h) (hF : Fresh h) : Uniq (syncAlloc h) := by
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := fresh_dead hF (Nat.le_refl _)
    simp [syncAlloc, e1, e2, e3, e4, e5, e6, cnt]
  · have := hU b
    simpa [syncAlloc, upd_ne _ _ _ _ hb] using this

theorem fresh_syncAlloc {h : Heap} (hF : Fresh h) : Fresh (syncAlloc h) := by
  intro b hb hl
  simp only [syncAlloc_nextBlk] at hb
  apply hF b (by omega)
  have hne : b ≠ h.nextBlk := by omega
  simpa [Heap.live, syncAlloc, upd_ne _ _ _ _ hne] using hl

theorem live_syncAlloc {h : Heap} (b : Nat) : (syncAlloc h).live b ↔ h.live b ∨ b = h.nextBlk := by
  by_cases hb : b = h.nextBlk
  · subst hb; simp [Heap.live, syncAlloc]
  · simp [Heap.live, syncAlloc, upd_ne _ _ _ _ hb, hb]

theorem winInv_syncAlloc {h : Heap} (hF : Fresh h) {st : InflateState} (hW : WinInv h st) : WinInv (syncAlloc h) st := by
  refine ⟨hW.wbits, ?_, hW.nullws, hW.ws, hW.hv, hW.wn, hW.eq⟩
  rcases hW.block with hn | ⟨w, a, hw, ha, hro, hsz⟩
  · exact Or.inl hn
  · have hwn : w ≠ h.nextBlk := by
      intro e; subst e
      obtain ⟨e0, -⟩ := fresh_dead hF (Nat.le_refl _)
      rw [ha] at e0; cases e0
    exact Or.inr ⟨w, a, hw, by rw [syncAlloc_bytes_ne h hwn]; exact ha, by simp [syncAlloc, upd_ne _ _ _ _ hwn, hro], hsz⟩

theorem good_syncAlloc {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) : Good (syncAlloc h) r zs z st := by
  obtain ⟨⟨hz, hs, zst, back, hm, za, zf⟩, ⟨wf, win, rq, bits, ptr⟩, hU, hF⟩ := hG
  exact ⟨⟨by simpa using hz, by simpa using hs, zst, back, hm, za, zf⟩,
    ⟨wf, winInv_syncAlloc hF win, rq, bits, ptr⟩, uniq_syncAlloc hU hF, fresh_syncAlloc hF⟩

theorem live_tmpFreed {h : Heap} (b : Nat) : (tmpFreed h).live b → (syncAlloc h).live b :=
  live_freeWin _ b

theorem freeBuf_run {H : Heap} {nb : Nat} {a : Array UInt8} (hb : H.bytes nb = some a) (hro : H.ro nb = false) :
    freeB (.ref (.blk nb) 0) H = .ok ((), freeWin H (.ref (.blk nb) 0)) := by
  rw [freeB_ok hb hro]; rfl

/-! ### The early returns -/

/-- **inflateSync, refusal.** If the state check fails (`StreamDom`: `NULL`, or a live record whose state is not a usable
inflate state) the call returns `Z_STREAM_ERROR`; nothing changes except that the local array `buf` was made and freed
(the block number is used up). -/
theorem inflateSync_check {h : Heap} (hF : Fresh h) {strm : ZStreamPtr} (hD : StreamDom h strm)
    (hN : ¬ Initialised h strm) :
    C.run (inflateSync strm) h = .ok (Z_STREAM_ERROR, tmpFreed h) := by
  have hD' : StreamDom (syncAlloc h) strm := by
    rcases hD with h0 | ⟨r, z, h0, hr, hc⟩
    · exact Or.inl h0
    · exact Or.inr ⟨r, z, h0, by simpa using hr, by simpa using hc⟩
  have hN' : ¬ Initialised (syncAlloc h) strm := by
    rintro ⟨r, zs, z, st, h0, hL⟩
    exact hN ⟨r, zs, z, st, h0, ⟨by simpa using hL.hz, by simpa using hL.hs, hL.zst, hL.back, hL.mode, hL.zalloc, hL.zfree⟩⟩
  show inflateSync strm h = _
  unfold inflateSync
  have hb : (syncAlloc h).bytes h.nextBlk = some (syncJunk h) := syncAlloc_bytes_buf h
  simp [bind_app, pure_app, allocLocalB_run h hF, notInit_check hD' hN', freeBuf_run hb (syncAlloc_ro_buf h), tmpFreed,
    syncBuf]

/-- **inflateSync, no input.** On an initialised stream with `avail_in = 0` and fewer than 8 bits in the bit buffer the
call returns `Z_BUF_ERROR`; nothing changes except that the local array `buf` was made and freed. -/
theorem inflateSync_buf_error {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (hav : z.avail_in = 0) (hb : st.bits < 8) :
    C.run (inflateSync (some r)) h = .ok (Z_BUF_ERROR, tmpFreed h) := by
  have hG' := good_syncAlloc hG
  have hL := hG'.live
  show inflateSync (some r) h = _
  unfold inflateSync
  have hbb : (syncAlloc h).bytes h.nextBlk = some (syncJunk h) := syncAlloc_bytes_buf h
  isimp [allocLocalB_run h hG.fresh, stateCheck_live hL, hL.zst, hG.live.hz, hG.live.hs, hav, hb,
    freeBuf_run hbb (syncAlloc_ro_buf h), tmpFreed, syncBuf]

/-- the part of `inflateSync` from the bit-buffer restore on, as a function of the state pointer -/
def syncFirst (st : InflateStatePtr) (buf : BPtr) (s : InflateState) : M Unit := do
  let h ← shr64 s.hold (s.bits &&& 7)
  wrS st fun s => { s with mode := SYNC, hold := h, bits := s.bits - (s.bits &&& 7) }
  let len ← cwhile (σ := UInt32)
    (fun len => do return ((← rdS st (·.bits)) >= 8, len))
    (fun len => do
      let s ← ldInflateState st
      store8 (← buf.add (len.toNat : Int)) s.hold.toUInt8
      wrS st fun s => { s with hold := s.hold >>> 8, bits := s.bits - 8 }
      pure (len + 1))
    0
  wrS st fun s => { s with «have» := 0 }
  let (_, hv) ← syncsearch 0 buf len
  wrS st fun s => { s with «have» := hv }

def syncDone (strm : ZStreamPtr) (st : InflateStatePtr) : M Int32 := do
    let flags ← rdS st (·.flags)
    let z ← ldZStream strm
    let in_ := z.total_in
    let out_ := z.total_out
    let _ ← inflateReset strm
    wrZ strm fun z => { z with total_in := in_, total_out := out_ }
    wrS st fun s => { s with flags := flags }
    if flags == -1 then wrS st fun s => { s with wrap := 0 }
    else wrS st fun s => { s with wrap := s.wrap &&& ~~~4 }
    let s ← ldInflateState st
    if s.wbits == 0 then
      if s.window != .null then
        ZFREEB strm s.window
        wrS st fun s => { s with window := .null }
      wrS st fun s => { s with wbits := 15 }
    setMode st TYPE
    return Z_OK

def syncTail (strm : ZStreamPtr) (st : InflateStatePtr) : M Int32 := do
    let z ← ldZStream strm
    let (len, hv) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
    wrS st fun s => { s with «have» := hv }
    let ni ← z.next_in.add (len.toNat : Int)
    wrZ strm fun z => { z with avail_in := z.avail_in - len, next_in := ni, total_in := z.total_in + len.toUInt64 }
    if (← rdS st (·.«have»)) != 4 then return Z_DATA_ERROR
    syncDone strm st

theorem bind_ite_unit {α : Type} (c : Prop) [Decidable c] (A : M Unit) (jp : Unit → M α) :
    (ite c A (pure ()) >>= jp) = ite c (A >>= jp) (jp ()) := by
  by_cases hc : c <;> simp [hc] <;> rfl

theorem bind_assoc_M {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h with
  | error e => rfl
  | ok p => rfl

theorem inflateSync_split (strm : ZStreamPtr) : inflateSync strm = (do
  let buf ← allocLocalB 4
  let r ← (do
    if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
    let z ← ldZStream strm
    let st ← castInflateState z.state
    let s ← ldInflateState st
    if z.avail_in == 0 && s.bits < 8 then return Z_BUF_ERROR
    if s.mode != SYNC then syncFirst st buf s
    syncTail strm st)
  freeB buf
  return r) := by
  unfold inflateSync syncFirst syncTail syncDone
  simp only [bind_assoc_M]

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Spec
open C

/-- The state record after `inflateReset`, the restored flags and the wrapper change of `inflateSync`, before the window
bits are looked at: the request is raw if no header was read (`flags = -1`), else the check bit is cleared. -/
def syncC (zs : Nat) (s : InflateState) : InflateState :=
  let sB := { resetKeepState zs (resetPre s) with flags := s.flags }
  if s.flags == -1 then { sB with wrap := 0 } else { sB with wrap := sB.wrap &&& ~~~4 }

/-- The state record after a successful `inflateSync` search: reset to wait for a block type (`TYPE`), the header flags
kept, a window size that no header ever gave set to 15 (the window is dropped then). -/
def syncOkState (zs : Nat) (s : InflateState) : InflateState :=
  let sC := syncC zs s
  { (if sC.wbits == 0 then { sC with window := .null, wbits := 15 } else sC) with mode := TYPE }

/-- The stream record after a successful `inflateSync` search: reset (`inflateReset`) but `total_in` and `total_out`
keep their values. `z` is the record after the search consumed its bytes. -/
def syncOkStream (z : ZStream) (s : InflateState) : ZStream :=
  { resetKeepStream z (resetPre s) with total_in := z.total_in, total_out := z.total_out }

/-- The heap after a successful `inflateSync` search, from the heap `H` (the stream record `z` after the search, the state
record `s`): the reset frees the window if its size is not the requested one; a window size of 0 frees the window. -/
def syncOkHeap (H : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Heap :=
  let X := setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)
  if (syncC zs s).wbits == 0 then freeWin X (syncC zs s).window else X

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- **inflateSync, found.** From a good stream (`zfree` the default) the part of `inflateSync` after the pattern is found
returns `Z_OK` with the heap `syncOkHeap`: reset, `total_in`/`total_out` kept, mode `TYPE`. -/
theorem syncDone_run {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hG : Good H r zs z s) (hf : z.zfree = .fn "zcfree") :
    syncDone (some r) (some (.tab zs)) H = .ok (Z_OK, syncOkHeap H r zs z s) := by
  have hL := hG.live
  have hwo : s.wbits = s.reqbits ∨ WindowOk H s.window := Or.inr (windowBlock hG.inv.win)
  have hz0 : r.get (resetHeap H s) = some z := by unfold resetHeap; split <;> simp [hL.hz]
  have hs0 : (resetHeap H s).istates zs = some s := by unfold resetHeap; split <;> simp [hL.hs]
  unfold syncDone
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs]
  rw [inflateReset_run hL hf hwo]
  have hrb : (resetPre s).wbits = s.reqbits := by unfold resetPre; split <;> simp_all
  have hwb := windowBlock (winInv_reset hG.inv.win hG.inv.reqbits)
  unfold syncOkHeap syncOkState syncOkStream syncC
  generalize resetPre s = sR at hrb hwb ⊢
  have hzN : r.get (setI (r.put (resetHeap H s) { resetKeepStream z sR with total_in := z.total_in, total_out := z.total_out }) zs
      (resetKeepState zs sR)) = some { resetKeepStream z sR with total_in := z.total_in, total_out := z.total_out } := by
    simp [hz0]
  by_cases hfl : s.flags = -1
  · by_cases h0 : sR.wbits = 0
    · rcases hwb with hn | ⟨b, a, hb, hba, hro⟩
      · isimp [hz0, hs0, resetKeepState, hfl, h0, hn, freeWin_null, setMode]
      · isimp [hz0, hs0, resetKeepState, hfl, h0, hb, setMode]
        rw [zfreeB_run (r := r) (z := { resetKeepStream z sR with total_in := z.total_in, total_out := z.total_out })
          (p := .ref (.blk b) 0) (by simp [hz0]) (by simpa [resetKeepStream] using hf) (Or.inr ⟨b, a, rfl, by simpa using hba, by simpa using hro⟩)]
        isimp [setMode, freeWin_istates]
    · isimp [hz0, hs0, resetKeepState, hfl, h0, setMode]
  · by_cases h0 : sR.wbits = 0
    · rcases hwb with hn | ⟨b, a, hb, hba, hro⟩
      · isimp [hz0, hs0, resetKeepState, hfl, h0, hn, freeWin_null, setMode]
      · isimp [hz0, hs0, resetKeepState, hfl, h0, hb, setMode]
        rw [zfreeB_run (r := r) (z := { resetKeepStream z sR with total_in := z.total_in, total_out := z.total_out })
          (p := .ref (.blk b) 0) (by simp [hz0]) (by simpa [resetKeepStream] using hf) (Or.inr ⟨b, a, rfl, by simpa using hba, by simpa using hro⟩)]
        isimp [setMode, freeWin_istates]
    · isimp [hz0, hs0, resetKeepState, hfl, h0, setMode]

/-! ### The invariants after a found pattern -/

theorem resetPre_win (st : InflateState) : (resetPre st).wsize = 0 ∧ (resetPre st).whave = 0 ∧ (resetPre st).wnext = 0 := by
  unfold resetPre; split <;> simp

theorem resetPre_wbits (st : InflateState) : (resetPre st).wbits = st.reqbits := by
  unfold resetPre; split <;> simp_all

theorem resetPre_strm (st : InflateState) : (resetPre st).strm = st.strm := by
  unfold resetPre; split <;> simp

theorem syncC_field (zs : Nat) (s : InflateState) :
    (syncC zs s).wbits = s.reqbits ∧ (syncC zs s).window = (resetPre s).window ∧ (syncC zs s).wsize = 0 ∧
    (syncC zs s).whave = 0 ∧ (syncC zs s).wnext = 0 ∧ (syncC zs s).reqbits = s.reqbits ∧ (syncC zs s).strm = s.strm ∧
    (syncC zs s).bits = 0 ∧ (syncC zs s).lens = s.lens ∧ (syncC zs s).work = s.work ∧ (syncC zs s).codes = s.codes := by
  obtain ⟨a1, a2, a3⟩ := resetPre_win s
  have a4 := resetPre_wbits s
  have a5 := resetPre_strm s
  have a6 : (resetPre s).reqbits = s.reqbits := reqbits_resetPre s
  have a7 : (resetPre s).lens = s.lens := by unfold resetPre; split <;> simp
  have a8 : (resetPre s).work = s.work := by unfold resetPre; split <;> simp
  have a9 : (resetPre s).codes = s.codes := by unfold resetPre; split <;> simp
  unfold syncC
  split <;> simp [resetKeepState, a1, a2, a3, a4, a5, a6, a7, a8, a9]

theorem syncC_ptr (zs : Nat) (s : InflateState) :
    (syncC zs s).next = .ref (.istate_codes zs) 0 ∧ (syncC zs s).lencode = .ref (.istate_codes zs) 0 ∧
    (syncC zs s).distcode = .ref (.istate_codes zs) 0 := by
  unfold syncC; split <;> simp [resetKeepState]

theorem syncOkState_eq0 {zs : Nat} {s : InflateState} (h0 : s.reqbits = 0) :
    syncOkState zs s = { syncC zs s with window := .null, wbits := 15, mode := TYPE } := by
  unfold syncOkState
  simp [(syncC_field zs s).1, h0]

theorem syncOkState_ne0 {zs : Nat} {s : InflateState} (h0 : s.reqbits ≠ 0) :
    syncOkState zs s = { syncC zs s with mode := TYPE } := by
  unfold syncOkState
  simp [(syncC_field zs s).1, h0]

/-- The state record after a found pattern satisfies the representation invariant on the heap after the reset. -/
theorem syncOk_inv {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} (hG : Good H r zs z s) :
    StInv (resetHeap H s) zs (syncOkState zs s) := by
  have hwf := wf_resetPre hG.inv.wf
  have hwr := winInv_reset hG.inv.win hG.inv.reqbits
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := syncC_field zs s
  obtain ⟨p1, p2, p3⟩ := syncC_ptr zs s
  have hwf' : s.WellFormed := hG.inv.wf
  have hrq := hG.inv.reqbits
  by_cases h0 : s.reqbits = 0
  · rw [syncOkState_eq0 h0]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold InflateState.WellFormed at hwf' ⊢
      simp only [f9, f10, f11]; exact hwf'
    · refine ⟨by simp, Or.inl rfl, fun _ => by simpa using f3, Or.inl (by simp [f3]), by simp [f3, f4], Or.inr ⟨by simp [f3], by simp [f5]⟩, fun hh => by simp [f3, f4] at hh⟩
    · simpa [f6] using hrq
    · simp [syncC, resetKeepState]; split <;> simp
    · exact ⟨⟨0, by simp [p1], by omega⟩, Or.inl ⟨0, 0, by simp [p2], by simp [p3], by omega, by omega⟩⟩
  · rw [syncOkState_ne0 h0]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold InflateState.WellFormed at hwf' ⊢
      simp only [f9, f10, f11]; exact hwf'
    · have hb : (resetPre s).wbits.toNat ≤ 15 := hwr.wbits
      refine ⟨by simpa [f1, resetPre_wbits] using hrq, ?_, fun hn => ?_, Or.inl (by simp [f3]), by simp [f3, f4], Or.inr ⟨by simp [f3], by simp [f5]⟩, fun hh => by simp [f3, f4] at hh⟩
      · have := hwr.block
        simpa [f2, f1, resetPre_wbits] using this
      · simp [f3]
    · simpa [f6] using hrq
    · simp [syncC, resetKeepState]; split <;> simp
    · exact ⟨⟨0, by simp [p1], by omega⟩, Or.inl ⟨0, 0, by simp [p2], by simp [p3], by omega, by omega⟩⟩

theorem winInv_of_null {H H' : Heap} {st : InflateState} (hW : WinInv H' st) (hn : st.window = .null) : WinInv H st :=
  ⟨hW.wbits, Or.inl hn, hW.nullws, hW.ws, hW.hv, hW.wn, hW.eq⟩

theorem stInv_of_null {H H' : Heap} {zs : Nat} {st : InflateState} (hI : StInv H' zs st) (hn : st.window = .null) :
    StInv H zs st :=
  ⟨hI.wf, winInv_of_null hI.win hn, hI.reqbits, hI.bits, hI.ptr⟩

theorem syncOk_window_null {zs : Nat} {s : InflateState} (h0 : s.reqbits = 0) : (syncOkState zs s).window = .null := by
  rw [syncOkState_eq0 h0]

/-- The window of the state is kept by a found pattern: it has the requested size, and the size is not 0. -/
def SyncKeeps (s : InflateState) : Prop := s.wbits = s.reqbits ∧ s.reqbits ≠ 0

theorem resetPre_window (st : InflateState) :
    (resetPre st).window = if st.wbits = st.reqbits then st.window else .null := by
  unfold resetPre; split <;> simp_all

/-- After a found pattern the stream is good again and the live blocks only shrink. -/
theorem syncDone_good {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hG : Good H r zs z s) :
    Good (syncOkHeap H r zs z s) r zs (syncOkStream z s) (syncOkState zs s) ∧
    (∀ b, (syncOkHeap H r zs z s).live b → H.live b) := by
  have hL := hG.live
  have hU : Uniq (resetHeap H s) := by
    unfold resetHeap; split
    · exact uniq_freeWin hG.uniq _
    · exact hG.uniq
  have hF : Fresh (resetHeap H s) := by
    unfold resetHeap; split
    · exact fresh_freeWin hG.fresh _
    · exact hG.fresh
  have hz0 : r.get (resetHeap H s) = some z := by unfold resetHeap; split <;> simp [hL.hz]
  have hs0 : (resetHeap H s).istates zs = some s := by unfold resetHeap; split <;> simp [hL.hs]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := syncC_field zs s
  have hmode : HEAD ≤ (syncOkState zs s).mode ∧ (syncOkState zs s).mode ≤ SYNC := by
    have : (syncOkState zs s).mode = TYPE := by unfold syncOkState; simp
    rw [this]; decide
  have hback : (syncOkState zs s).strm = some r := by
    have : (syncOkState zs s).strm = s.strm := by
      unfold syncOkState; simp [f7]
      split <;> simp [f7]
    rw [this]; exact hL.back
  have hX : Good (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) r zs (syncOkStream z s)
      (syncOkState zs s) :=
    good_set hz0 hs0 hU hF (by simp [syncOkStream, resetKeepStream, hL.zst]) (by simpa [syncOkStream, resetKeepStream] using hL.zalloc)
      (by simpa [syncOkStream, resetKeepStream] using hL.zfree) hback hmode (syncOk_inv hG)
  have hShape : Shape (resetHeap H s) (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) :=
    (shape_put hz0 _).trans (shape_setI (by simpa using hs0) _)
  have hlive0 : ∀ b, (resetHeap H s).live b → H.live b := by
    intro b hb
    unfold resetHeap at hb; split at hb
    · exact live_freeWin _ b hb
    · exact hb
  by_cases h0 : s.reqbits = 0
  · have hc : ((syncC zs s).wbits == 0) = true := by simp [f1, h0]
    have hHeap : syncOkHeap H r zs z s = freeWin (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) (resetPre s).window := by
      unfold syncOkHeap; simp [hc, f2]
    rw [hHeap]
    have hwn : (syncOkState zs s).window = .null := syncOk_window_null h0
    exact ⟨⟨⟨by simpa using hX.live.hz, by simpa using hX.live.hs, hX.live.zst, hX.live.back, hX.live.mode, hX.live.zalloc, hX.live.zfree⟩,
      stInv_of_null hX.inv hwn, uniq_freeWin hX.uniq _, fresh_freeWin hX.fresh _⟩,
      fun b hb => hlive0 b ((hShape.live b).1 (live_freeWin _ b hb))⟩
  · have hc : ¬ ((syncC zs s).wbits == 0) = true := by simp [f1, h0]
    have hHeap : syncOkHeap H r zs z s = setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s) := by
      unfold syncOkHeap; simp [hc]
    rw [hHeap]
    exact ⟨hX, fun b hb => hlive0 b ((hShape.live b).1 hb)⟩

/-- Ownership after a found pattern: only the window block can be freed (`¬ SyncKeeps`); nothing is allocated. -/
theorem syncDone_owns {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hG : Good H r zs z s) {S : Nat → Prop} (hO : H.Owns S) :
    (syncOkHeap H r zs z s).Owns (fun b => S b ∧ ¬ (¬ SyncKeeps s ∧ WinBlk s b)) := by
  have hL := hG.live
  have hz0 : r.get (resetHeap H s) = some z := by unfold resetHeap; split <;> simp [hL.hz]
  have hs0 : (resetHeap H s).istates zs = some s := by unfold resetHeap; split <;> simp [hL.hs]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := syncC_field zs s
  have hShape : Shape (resetHeap H s) (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) :=
    (shape_put hz0 _).trans (shape_setI (by simpa using hs0) _)
  have hO2 := hShape.owns (resetHeap_owns hG.uniq hG.inv.win hO)
  have hwb := windowBlock (winInv_reset hG.inv.win hG.inv.reqbits)
  have hrw := resetPre_window s
  by_cases h0 : s.reqbits = 0
  · have hc : ((syncC zs s).wbits == 0) = true := by simp [f1, h0]
    have hHeap : syncOkHeap H r zs z s = freeWin (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) (resetPre s).window := by
      unfold syncOkHeap; simp [hc, f2]
    rw [hHeap]
    rcases hwb with hn | ⟨w, a, hw, hba, hro⟩
    · rw [hn, freeWin_null]
      intro b; rw [hO2 b]
      by_cases hwr : s.wbits = s.reqbits
      · rw [hwr] at hrw
        simp only [ite_true] at hrw
        have : ¬ WinBlk s b := by
          intro hb; unfold WinBlk at hb; rw [hrw] at hn; simp [hb] at hn
        simp [SyncKeeps, this, hwr]
      · simp [SyncKeeps, hwr]
    · have hwr : s.wbits = s.reqbits := by
        by_cases hh : s.wbits = s.reqbits
        · exact hh
        · rw [ite_eq_right hh] at hrw; rw [hrw] at hw; cases hw
      rw [ite_eq_left hwr] at hrw
      have hUX : Uniq (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)) :=
        hShape.uniq (by
          unfold resetHeap; split
          · exact uniq_freeWin hG.uniq _
          · exact hG.uniq)
      have hbX : (setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s)).bytes w = some a := by simpa using hba
      have := owns_freeWin hUX hbX hO2
      rw [hw]
      intro b
      rw [this b]
      have hws : s.window = .ref (.blk w) 0 := by rw [← hrw]; exact hw
      have hWB : WinBlk s b ↔ b = w := by
        unfold WinBlk; rw [hws]
        constructor
        · intro hh; exact (BRef.blk.inj (Ptr.ref.inj hh).1).symm
        · intro hh; rw [hh]
      simp [SyncKeeps, hwr, h0, hWB]
  · have hc : ¬ ((syncC zs s).wbits == 0) = true := by simp [f1, h0]
    have hHeap : syncOkHeap H r zs z s = setI (r.put (resetHeap H s) (syncOkStream z s)) zs (syncOkState zs s) := by
      unfold syncOkHeap; simp [hc]
    rw [hHeap]
    intro b; rw [hO2 b]
    simp [SyncKeeps, h0]

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Spec
open C

/-- The search state `g` is consistent with the bytes `w` seen so far: either the pattern has not occurred and `g` is the
longest proper prefix of it that ends `w` (`SyncSt`), or the pattern has occurred in `w` and `g = 4`. -/
def SyncAt (g : UInt32) (w : List UInt8) : Prop := SyncSt g w ∨ (g = 4 ∧ syncPat <:+: w)

/-- `p + n` for a pointer into a block (`NULL` stays `NULL`: only `n = 0` occurs there). -/
def syncAdv (p : BPtr) (n : Nat) : BPtr := match p with | .null => .null | .ref r o => .ref r (o + n)

/-- The stream record after the search consumed `N` bytes of input: `avail_in` down, `next_in` and `total_in` up. -/
def syncAdvance (z : ZStream) (N : UInt32) : ZStream :=
  { z with avail_in := z.avail_in - N, next_in := syncAdv z.next_in N.toNat, total_in := z.total_in + N.toUInt64 }

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem syncsearch_at {h : Heap} {p : BPtr} {len : UInt32} {bs : List UInt8} (I : SyncIn h p len bs)
    {g : UInt32} {w : List UInt8} (hA : SyncAt g w) :
    ∃ N G, syncsearch g p len h = .ok ((N, G), h) ∧ N.toNat ≤ len.toNat ∧
      (G = 4 → syncPat <:+: w ++ bs.take N.toNat ∧ ∀ L', L' < N.toNat → ¬ syncPat <:+: w ++ bs.take L') ∧
      (G ≠ 4 → N = len ∧ SyncSt G (w ++ bs)) := by
  rcases hA with hs | ⟨rfl, hw⟩
  · obtain ⟨N, G, hr, h1, h2, h3⟩ := syncsearch_spec I hs
    refine ⟨N, G, hr, h1, ?_, h3⟩
    intro h4
    obtain ⟨-, a, b⟩ := h2 h4
    exact ⟨List.IsSuffix.isInfix a, b⟩
  · have hlen := syncIn_length I
    rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have := syncsearch_run (r := .blk b) (h := h) (a := a) (o := o) (len := len) 4 hg hl
      rw [syncScan_ge (by decide)] at this
      refine ⟨0, 4, by simpa using this, by simp, fun _ => ⟨by simpa using hw, fun L' hL' => by simp at hL'⟩, fun h4 => absurd rfl h4⟩
    · refine ⟨0, 4, syncsearch_null 4 h, by simp, fun _ => ⟨by simpa using hw, fun L' hL' => by simp at hL'⟩, fun h4 => absurd rfl h4⟩

/-- Reading the search result into the stream: advancing the input pointer by `N ≤ len` bytes. -/
theorem syncAdd_run {H : Heap} {p : BPtr} {len : UInt32} {bs : List UInt8} (I : SyncIn H p len bs) {N : UInt32}
    (hN : N.toNat ≤ len.toNat) {H' : Heap} (hb : H'.bytes = H.bytes) :
    Ptr.add p (N.toNat : Int) H' = .ok (syncAdv p N.toNat, H') := by
  rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hg' : Space.get H' (BRef.blk b) = some a := by simpa [Space.get, hb] using hg
    exact Ptr.add_nat_ok (r := BRef.blk b) hg' (by omega)
  · have : N.toNat = 0 := by simpa using hN
    rw [this]; rfl

/-- The state record after the search: only `have` changes. -/
def syncHave (s : InflateState) (G : UInt32) : InflateState := { s with «have» := G }

theorem good_syncSearch {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hG : Good H r zs z s) (N : UInt32) (G : UInt32) :
    Good (setI (r.put H (syncAdvance z N)) zs (syncHave s G)) r zs (syncAdvance z N) (syncHave s G) :=
  hG.setZI (by simp [syncAdvance]) (by simpa [syncAdvance] using hG.live.zalloc)
    (by simpa [syncAdvance] using hG.live.zfree) (by simp [syncHave]) (by simpa [syncHave] using hG.live.mode)
    (hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG.inv.bits rfl rfl rfl)

/-- **The search step of `inflateSync`.** On a stream in the search (`Good`, with the state's `have` consistent with the
bytes `w` seen so far, `SyncAt`) and an input `next_in[0 .. avail_in)` (`SyncIn`), the part of `inflateSync` from the call
of `syncsearch` on runs without a fault. It stores the search result in `have`, consumes `N` bytes (`syncAdvance`) and
returns `Z_DATA_ERROR` if the pattern is not complete (`G ≠ 4`, and then all the input was consumed), else `Z_OK` after the
reset of the stream (`syncOkHeap`). -/
theorem syncTail_run {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs w : List UInt8}
    (hG : Good H r zs z s) (hf : z.zfree = .fn "zcfree") (hI : SyncIn H z.next_in z.avail_in bs)
    (hA : SyncAt s.«have» w) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → syncPat <:+: w ++ bs.take N.toNat ∧ ∀ L', L' < N.toNat → ¬ syncPat <:+: w ++ bs.take L') ∧
      (G ≠ 4 → N = z.avail_in ∧ SyncSt G (w ++ bs)) ∧
      Good (setI (r.put H (syncAdvance z N)) zs (syncHave s G)) r zs (syncAdvance z N) (syncHave s G) ∧
      (G ≠ 4 → syncTail (some r) (some (.tab zs)) H =
        .ok (Z_DATA_ERROR, setI (r.put H (syncAdvance z N)) zs (syncHave s G))) ∧
      (G = 4 → syncTail (some r) (some (.tab zs)) H =
        .ok (Z_OK, syncOkHeap (setI (r.put H (syncAdvance z N)) zs (syncHave s G)) r zs (syncAdvance z N) (syncHave s G))) := by
  have hL := hG.live
  obtain ⟨N, G, hse, hN, h4, h3⟩ := syncsearch_at hI hA
  have hG1 := good_syncSearch hG N G
  refine ⟨N, G, hN, h4, h3, hG1, fun hne => ?_, fun he => ?_⟩
  · unfold syncTail
    isimp [hL.hz, hL.hs, hse, syncAdd_run hI hN (H' := setI H zs { s with «have» := G }) rfl, syncAdvance, syncHave, hne]
  · subst he
    unfold syncTail
    have hdone := syncDone_run (hG1) (by simpa [syncAdvance] using hf)
    isimp [hL.hz, hL.hs, hse, syncAdd_run hI hN (H' := setI H zs { s with «have» := 4 }) rfl]
    simpa [syncAdvance, syncHave] using hdone

end Zlib.Inflate.Proofs
