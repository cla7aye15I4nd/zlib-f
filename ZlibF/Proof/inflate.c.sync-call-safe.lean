import ZlibF.Proof.«inflate.c.call-safety»
import ZlibF.Proof.«inflate.c.sync-invariant»
import ZlibF.Proof.«inflate.c.sync-default-public»
import ZlibF.Math.«heap-table-updates»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.buffer-frame-compose»
import ZlibF.Proof.«inflate.c.leave-output-footprint»

/-!
# inflate.c: the safety clause of `inflateSync`

From the history invariant, `inflateSync` returns. Its heap is the caller's
heap with the local array made and freed, the stream and decoder records
rewritten, and the window freed exactly when the recovery reset changes the
width (`wbits != reqbits`). The frame and the ownership ledger then follow as
for `inflateReset`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A width as the `int` argument of `inflateReset2`. -/
def syncWidth (k : UInt32) : Int32 := Int32.ofNat k.toNat

theorem i2u_syncWidth {k : UInt32} (small : k.toNat ≤ 15) : i2u (syncWidth k) = k := by
  have key : ∀ n : Nat, n < 16 → i2u (Int32.ofNat n) = UInt32.ofNat n := by decide
  unfold syncWidth
  rw [key _ (by omega)]
  exact UInt32.ofNat_toNat

theorem InflateInv.wbits_small {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s) : s.wbits.toNat ≤ 15 := by
  rcases current.config.window with range | ⟨zero, _⟩
  · exact range.2
  · rw [zero]
    decide

theorem InflateInv.zero_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s) (zero : s.wbits = 0) : s.window = .null := by
  rcases current.config.window with range | ⟨_, null, _⟩
  · rw [zero] at range
    exact absurd range.1 (by decide)
  · exact null

/-- The successful recovery heap is a reset of the records, with the window
freed exactly when the width changes. -/
theorem syncOkHeap_reset2 {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r zs z s) :
    syncOkHeap h r zs z s = setI (r.put (reset2Heap h (syncWidth s.reqbits) s) (syncOkStream z s)) zs
        (syncOkState zs s) ∧
      (syncOkState zs s).window = if s.wbits ≠ i2u (syncWidth s.reqbits) then .null else s.window := by
  have width := i2u_syncWidth current.good.inv.reqbits
  have reset : resetHeap h s = reset2Heap h (syncWidth s.reqbits) s := by
    simp only [resetHeap, reset2Heap, width]
  have syncWindow : (syncC zs s).window = if s.wbits = s.reqbits then s.window else .null := by
    rw [(syncC_field zs s).2.1, resetPre_window]
  rw [width]
  by_cases zero : s.reqbits = 0
  · have cleared : (syncC zs s).window = .null := by
      rw [syncWindow]
      by_cases same : s.wbits = s.reqbits
      · rw [if_pos same]
        exact current.zero_window (same.trans zero)
      · rw [if_neg same]
    have test : ((syncC zs s).wbits == 0) = true := by
      rw [(syncC_field zs s).1, zero]
      rfl
    refine ⟨?_, ?_⟩
    · unfold syncOkHeap
      simp only [test, ↓reduceIte, cleared, reset]
      rfl
    · unfold syncOkState
      simp only [test, ↓reduceIte]
      by_cases same : s.wbits = s.reqbits
      · simp only [same, ne_eq, not_true_eq_false, ↓reduceIte]
        exact (current.zero_window (same.trans zero)).symm
      · simp only [ne_eq, same, not_false_eq_true, ↓reduceIte]
  · have test : ((syncC zs s).wbits == 0) = false := by
      rw [(syncC_field zs s).1]
      simpa using zero
    refine ⟨?_, ?_⟩
    · unfold syncOkHeap
      simp only [test, Bool.false_eq_true, ↓reduceIte, reset]
    · rw [syncOkState_ne0 zero]
      change (syncC zs s).window = _
      rw [syncWindow]
      by_cases same : s.wbits = s.reqbits
      · simp only [same, ne_eq, not_true_eq_false, ↓reduceIte]
      · simp only [same, ne_eq, not_false_eq_true, ↓reduceIte]

/-- The search and its recovery, from a decoder in `SYNC`: the records are
rewritten and the window is freed exactly when the width changes. -/
theorem syncTail_total {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r zs z s) (mode : s.mode = SYNC)
    (range : z.next_in = .null ∨ ∃ xs, Bytes h z.next_in z.avail_in.toNat xs)
    (nonnull : z.next_in = .null → z.avail_in = 0) :
    ∃ rc after stream state wb, C.run (syncTail (some r) (some (.tab zs))) h = .ok (rc, after) ∧
      Good after r zs stream state ∧ after = setI (r.put (reset2Heap h wb s) stream) zs state ∧
      state.window = (if s.wbits ≠ i2u wb then .null else s.window) := by
  obtain ⟨used, found, search, bound⟩ := syncsearch_public_readable range nonnull s.«have»
  obtain ⟨next, advance⟩ := sync_public_input_add range nonnull bound zs { s with «have» := found }
  let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
  let state := syncHave s found
  let heap := setI (r.put h stream) zs state
  have searched : InflateInv heap r zs stream state := current.sync_search_state mode used found next
  have tailPrefix : C.run (syncTail (some r) (some (.tab zs))) h =
      (if found != 4 then pure Z_DATA_ERROR else syncDone (some r) (some (.tab zs))) heap := by
    unfold C.run syncTail
    simp only [bind_app, ldZ_eq, rdI_eq, current.good.live.hs, search,
      wrI_eq, advance, wrZ_eq, ZStreamRef.get_setI, current.good.live.hz,
      setI_istates_same, ZStreamRef.put_setI]
    rfl
  have keep : reset2Heap h (syncWidth s.wbits) s = h := by
    simp only [reset2Heap, i2u_syncWidth current.wbits_small, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
  by_cases complete : found = 4
  · subst found
    obtain ⟨doneRun, done⟩ := searched.sync_done
    obtain ⟨doneHeap, doneWindow⟩ := syncOkHeap_reset2 searched
    have stateWidth : state.reqbits = s.reqbits := rfl
    have stateReset : reset2Heap heap (syncWidth state.reqbits) state =
        setI (r.put (reset2Heap h (syncWidth s.reqbits) s) stream) zs state := by
      unfold reset2Heap
      change (if s.wbits != i2u (syncWidth s.reqbits) then freeWin heap s.window else heap) = _
      split <;> simp only [heap, setI_freeWin, ZStreamRef.put_freeWin]
    refine ⟨Z_OK, syncOkHeap heap r zs stream state, syncOkStream stream state, syncOkState zs state,
      syncWidth s.reqbits, ?_, done.good, ?_, ?_⟩
    · rw [tailPrefix]
      simpa only [C.run, bne_self_eq_false, Bool.false_eq_true, ite_false] using doneRun
    · rw [doneHeap, stateReset]
      simp only [ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI]
    · exact doneWindow
  · refine ⟨Z_DATA_ERROR, heap, stream, state, syncWidth s.wbits, ?_, searched.good, ?_, ?_⟩
    · rw [tailPrefix]
      simp [complete, pure_app]
    · rw [keep]
    · simp only [i2u_syncWidth current.wbits_small, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl

/-- Two frees commute. -/
theorem freeWin_comm (H : Heap) (p q : BPtr) : freeWin (freeWin H p) q = freeWin (freeWin H q) p := by
  rcases p with _ | ⟨p, op⟩ <;> rcases q with _ | ⟨q, oq⟩ <;> try rfl
  cases p <;> cases q <;> try rfl
  all_goals (cases op <;> cases oq <;> try rfl)
  rename_i a b
  by_cases same : a = b
  · subst same
    rfl
  · simp only [freeWin, upd]
    rw [C.Tbl.set_comm _ same]

theorem freeWin_reset2Heap (H : Heap) (p : BPtr) (wb : Int32) (s : InflateState) :
    freeWin (reset2Heap H wb s) p = reset2Heap (freeWin H p) wb s := by
  unfold reset2Heap
  split
  · exact freeWin_comm _ _ _
  · rfl

/-- `inflateSync` from the history invariant returns, with the records
rewritten and the window freed exactly when the width changes, on the heap
where the local array was made and freed. -/
theorem inflateSync_total {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state wb, C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      Good after r i stream state ∧
      after = setI (r.put (reset2Heap (tmpFreed h) wb s) stream) i state ∧
      state.window = (if s.wbits ≠ i2u wb then .null else s.window) := by
  obtain ⟨z0, get0, nonnull, range⟩ := arguments
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have readable : z.next_in = .null ∨ ∃ xs, Bytes h z.next_in z.avail_in.toNat xs := by
    rcases range with null | ⟨bytes, _⟩
    · exact Or.inl null
    · exact Or.inr bytes
  have allocated := current.sync_alloc
  have localGet := syncAlloc_bytes_buf h
  have localSize : (syncJunk h).size = 4 := by simp [syncJunk]
  have localWrite := syncAlloc_ro_buf h
  have base : InflateInv (tmpFreed h) r i z s := allocated.free_local localGet localSize
  have keep : reset2Heap (tmpFreed h) (syncWidth s.wbits) s = tmpFreed h := by
    simp only [reset2Heap, i2u_syncWidth current.wbits_small, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
  by_cases empty : z.avail_in = 0 ∧ s.bits < 8
  · refine ⟨Z_BUF_ERROR, tmpFreed h, z, s, syncWidth s.wbits,
      inflateSync_buf_error current.good empty.1 empty.2, base.good, ?_, ?_⟩
    · rw [keep, ZStreamRef.put_self base.good.live.hz, tcSetI_same base.good.live.hs]
    · simp only [i2u_syncWidth current.wbits_small, ne_eq, not_true_eq_false, ↓reduceIte]
  have readable0 : z.next_in = .null ∨ ∃ xs, Bytes (syncAlloc h) z.next_in z.avail_in.toNat xs := by
    rcases callerRange_syncAlloc current.good.fresh range with null | ⟨bytes, _⟩
    · exact Or.inl null
    · exact Or.inr bytes
  by_cases resumed : s.mode = SYNC
  · obtain ⟨rc, middle, stream, state, wb, tailRun, good, heapEq, window⟩ :=
      syncTail_total allocated resumed readable0 nonnull
    have separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ h.nextBlk :=
      win_ne_buf current.good.fresh current.good.inv.win
    have get : middle.bytes h.nextBlk = some (syncJunk h) := by
      rw [heapEq, setI_bytes, ZStreamRef.put_bytes]
      unfold reset2Heap
      split
      · cases windowEq : s.window with
        | null => exact localGet
        | ref ref off =>
          cases ref <;> try exact localGet
          rename_i w
          cases off with
          | zero => simpa only [freeWin, upd_ne _ _ _ _ (separate w windowEq).symm] using localGet
          | succ => exact localGet
      · exact localGet
    have write : middle.ro h.nextBlk = false := by
      rw [heapEq, setI_ro, ZStreamRef.put_ro]
      unfold reset2Heap
      split
      · rw [freeWin_ro]
        exact localWrite
      · exact localWrite
    have free := freeBuf_run get write
    simp only [C.run] at tailRun
    refine ⟨rc, freeWin middle (syncBuf h), stream, state, wb, ?_, ?_, ?_, window⟩
    · unfold C.run
      rw [inflateSync_split]
      simp [bind_app, syncBuf, allocLocalB_run h current.good.fresh, stateCheck_live allocated.good.live,
        ldZ_eq, allocated.good.live.hz, allocated.good.live.zst, castI, ldI_eq, current.good.live.hs,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty, bne_iff_ne, resumed, pure_app, tailRun, free]
    · exact good_freeBuf good (nb := h.nextBlk) (fun w hw same => by
        rw [window] at hw
        split at hw
        · cases hw
        · exact separate w hw same)
    · rw [heapEq, ← setI_freeWin, ← ZStreamRef.put_freeWin, freeWin_reset2Heap]
      rfl
  · have separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ h.nextBlk :=
      win_ne_buf current.good.fresh current.good.inv.win
    have firstRun := syncFirst_run allocated.good.live.hs localGet localSize localWrite
      allocated.good.inv.bits
    have firstState := allocated.sync_first localGet separate
    have firstReadable := sync_readable_first (zs := i) (s := s) current.good.fresh readable
    obtain ⟨rc, middle, stream, state, wb, tailRun, good, heapEq, window⟩ :=
      syncTail_total firstState rfl firstReadable nonnull
    have get : middle.bytes h.nextBlk = some (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)) := by
      rw [heapEq, setI_bytes, ZStreamRef.put_bytes]
      have firstGet : (syncFirstHeap (syncAlloc h) i h.nextBlk s (syncJunk h)).bytes h.nextBlk =
          some (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)) := by
        simp only [syncFirstHeap, upd_same]
      unfold reset2Heap
      split
      · cases windowEq : (syncFirstState s).window with
        | null => exact firstGet
        | ref ref off =>
          cases ref <;> try exact firstGet
          rename_i w
          cases off with
          | zero =>
            simpa only [freeWin, upd_ne _ _ _ _ (separate w windowEq).symm] using firstGet
          | succ => exact firstGet
      · exact firstGet
    have size : (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)).size = 4 := by
      rw [fillBuf_size]
      exact localSize
    have write : middle.ro h.nextBlk = false := by
      rw [heapEq, setI_ro, ZStreamRef.put_ro]
      have firstWrite : (syncFirstHeap (syncAlloc h) i h.nextBlk s (syncJunk h)).ro h.nextBlk = false :=
        localWrite
      unfold reset2Heap
      split
      · rw [freeWin_ro]
        exact firstWrite
      · exact firstWrite
    have free := freeBuf_run get write
    simp only [C.run] at tailRun
    refine ⟨rc, freeWin middle (syncBuf h), stream, state, wb, ?_, ?_, ?_, window⟩
    · unfold C.run
      rw [inflateSync_split]
      simp [bind_app, syncBuf, allocLocalB_run h current.good.fresh, stateCheck_live allocated.good.live,
        ldZ_eq, allocated.good.live.hz, allocated.good.live.zst, castI, ldI_eq, current.good.live.hs,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty, bne_iff_ne, resumed, firstRun, tailRun,
        free, pure_app]
    · exact good_freeBuf good (nb := h.nextBlk) (fun w hw same => by
        rw [window] at hw
        split at hw
        · cases hw
        · exact separate w hw same)
    · have freedFirst : freeWin (syncFirstHeap (syncAlloc h) i h.nextBlk s (syncJunk h)) (syncBuf h) =
          setI (tmpFreed h) i (syncFirstState s) := by
        simp only [freeWin, syncBuf, syncFirstHeap, setI, tmpFreed, upd_upd]
      rw [heapEq, ← setI_freeWin, ← ZStreamRef.put_freeWin, freeWin_reset2Heap, freedFirst]
      have reset : reset2Heap (setI (tmpFreed h) i (syncFirstState s)) wb (syncFirstState s) =
          setI (reset2Heap (tmpFreed h) wb s) i (syncFirstState s) := by
        unfold reset2Heap
        change (if s.wbits != i2u wb then freeWin (setI (tmpFreed h) i (syncFirstState s)) s.window
          else setI (tmpFreed h) i (syncFirstState s)) = _
        split <;> simp only [setI_freeWin]
      rw [reset, ZStreamRef.put_setI, setI_setI]

/-- `inflateSync`: the frame and ownership ledger of `StreamSequenceSafety`,
including a window freed by the recovery reset. -/
theorem inflateSync_call_safe (r : ZStreamRef) : InflateCallSafe r (.inflateSync (some r)) := by
  intro h i z s current _ arguments
  obtain ⟨rc, after, stream, state, wb, run, good, heapEq, window⟩ := inflateSync_total current arguments
  have fresh := current.good.fresh
  have base : InflateInv (tmpFreed h) r i z s :=
    current.sync_alloc.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
  have shape := sync_tmp_freed_shape fresh
  have getZ : r.get (reset2Heap (tmpFreed h) wb s) = some z := by
    unfold reset2Heap
    split
    · rw [ZStreamRef.get_freeWin]
      exact base.good.live.hz
    · exact base.good.live.hz
  have getS : (reset2Heap (tmpFreed h) wb s).istates i = some s := by
    unfold reset2Heap
    split
    · rw [freeWin_istates]
      exact base.good.live.hs
    · exact base.good.live.hs
  have owns : ∀ S, (tmpFreed h).Owns S →
      after.Owns (fun b => S b ∧ ¬ (s.wbits ≠ i2u wb ∧ WinBlk s b)) := by
    intro S own
    rw [heapEq]
    exact ((shape_put getZ stream).trans (shape_setI (by simpa using getS) state)).owns
      (reset2Heap_owns base.good.uniq base.good.inv.win own)
  obtain ⟨frame, ledger⟩ :=
    reset2_public_resources base.good good heapEq owns window (.inflateSync (some r)) rfl
  have owned : ∀ b, StreamOwned (tmpFreed h) r b ↔ StreamOwned h r b := by
    intro b
    rw [base.good.streamOwned_iff, current.good.streamOwned_iff]
  refine ⟨rc, after, heapCall_of_actual_run run default, ⟨?_, ?_⟩, ?_⟩
  · change Frame h after _
    have later : Frame (tmpFreed h) after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
          StreamHeaderRecord h r (.inflateSync (some r)) b) := by
      apply inflate_frame_mono frame.1
      intro b changed
      rcases changed with root | own | record
      · exact Or.inl root
      · exact Or.inr (Or.inl ((owned b).mp own))
      · rcases record with getHeader | ⟨_, _, _, _, _, _, _, _, flush, call⟩
        · cases getHeader
    exact frame_trans_shape (tmp_freed_buffer_frame fresh _ []).1 later shape
  · intro region member
    cases member
  · intro b
    rw [ledger b]
    simp only []
    rw [shape.live b, owned b]

#print axioms inflateSync_call_safe
end Zlib.Inflate.Proofs
