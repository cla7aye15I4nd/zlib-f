import ZlibF.Proof.«deflate.c.init.frame»

/-! # deflate.c: actual default allocation failure and cleanup heap -/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

def failureState (ph : Heap) (r : ZStreamRef) : DeflateState :=
  { bufferState ph (baseState r) with status := FINISH_STATE }

def failureStream (h : Heap) (z : ZStream) (m : BPtr) : ZStream :=
  { stateStream z h.nextBlk with msg := m }

def failureMsgHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  let ph := publishedHeap h r z
  r.put (setD (buffersHeap ph) h.nextBlk (failureState ph r)) (failureStream h z m)

def failureHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  endHeap (failureMsgHeap h r z m) r h.nextBlk (failureStream h z m)
    (failureState (publishedHeap h r z) r)

def clearDHeap (h : Heap) (ds : Nat) : Heap := { h with dstates := upd h.dstates ds none }

theorem failure_heap_eq (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    failureHeap h r z m = clearDHeap
      (r.put (rollbackBuffers (publishedHeap h r z) (failureMsgHeap h r z m))
        { failureStream h z m with state := none }) h.nextBlk := by
  unfold failureHeap endHeap clearDHeap
  rw [ZStreamRef.put_dstates, (rollback_stable _ _).dstates]
  rfl

theorem get_failure_raw {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) :
    r.get (setD (buffersHeap (publishedHeap h r z)) h.nextBlk
      (failureState (publishedHeap h r z) r)) = some (stateStream z h.nextBlk) := by
  simp [publishedHeap, ZStreamRef.get_put_same hz]

theorem get_failure_message {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (m : BPtr) :
    r.get (failureMsgHeap h r z m) = some (failureStream h z m) := by
  exact ZStreamRef.get_put_same (get_failure_raw hz) _

theorem memory_message (h : Heap) : ∃ m, ERR_MSG Z_MEM_ERROR h = .ok (m, h) := by
  obtain ⟨i, hr, _⟩ := Zlib.Zutil.Proofs.strLit_run h
    (Zlib.Zutil.Spec.errText Z_MEM_ERROR.toInt) (Zlib.Zutil.Proofs.errText_lit _)
  refine ⟨.ref (.str i) 0, ?_⟩
  unfold ERR_MSG
  rw [Zlib.Zutil.Proofs.zError_eval]
  exact hr

/-- The actual failed-buffer branch sets FINISH_STATE, obtains the actual
error literal and invokes cleanup on the partially constructed stream. -/
theorem finish_failure {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hd : DefAlloc z) (level : Int32)
    (bad : ((bufferPointers (publishedHeap h r z)).1 == .null ||
      (bufferPointers (publishedHeap h r z)).2.1 == .null ||
      (bufferPointers (publishedHeap h r z)).2.2.1 == .null ||
      (bufferPointers (publishedHeap h r z)).2.2.2 == .null) = true) :
    ∃ m, finish (some r) (some (.tab h.nextBlk)) level (bufferPointers (publishedHeap h r z))
        (setD (buffersHeap (publishedHeap h r z)) h.nextBlk
          (bufferState (publishedHeap h r z) (baseState r))) =
      .ok (Z_MEM_ERROR, failureHeap h r z m) := by
  let ph := publishedHeap h r z
  let gf := setD (buffersHeap ph) h.nextBlk (failureState ph r)
  obtain ⟨m, hm⟩ := memory_message gf
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw hz
  have hzM := get_failure_message hz m
  have hl : DLive (failureMsgHeap h r z m) r h.nextBlk (failureStream h z m) (failureState ph r) := by
    refine ⟨hzM, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [failureMsgHeap, ph]
    · simp [failureState, GoodStatus]
    · simpa [failureStream, stateStream] using (show z.zalloc ≠ .null by rw [hd.1]; decide)
    · simpa [failureStream, stateStream] using (show z.zfree ≠ .null by rw [hd.2]; decide)
  obtain ⟨hw, hp, hq, hb, hwb, hpq⟩ := buffers_freeable ph
  have release := end_partial_run hl (by simpa [failureStream, stateStream] using hd.2)
    (by simpa [FreeableB, failureMsgHeap, failureState, bufferState, bufferPointers] using hb)
    (by simpa [FreeableB, failureMsgHeap, failureState, bufferState, bufferPointers] using hw)
    (by simpa [FreeableW, failureMsgHeap, failureState, bufferState, bufferPointers] using hq)
    (by simpa [FreeableW, failureMsgHeap, failureState, bufferState, bufferPointers] using hp)
    (by simpa [failureState, bufferState, bufferPointers] using hwb)
    (by simpa [failureState, bufferState, bufferPointers] using hpq)
  refine ⟨m, ?_⟩
  unfold finish
  simp only []
  rw [bad]
  simp only [ite_true, bind_app, wrD_eq, setD_dstates_same, setD_setD]
  change (do
    let m ← ERR_MSG Z_MEM_ERROR
    zwr (some r) (fun z => { z with msg := m })
    let _ ← deflateEnd (some r)
    pure Z_MEM_ERROR) gf = _
  rw [bind_app, hm]
  simp only [bind_app, zwr_eq, hzF]
  change (do let _ ← deflateEnd (some r); pure Z_MEM_ERROR) (failureMsgHeap h r z m) = _
  rw [bind_app, release]
  rfl

theorem slot_clearD_except (h : Heap) (ds x : Nat) (hn : x ≠ ds) :
    SlotSame h (clearDHeap h ds) x := by
  simp [SlotSame, clearDHeap, upd_ne _ _ _ _ hn]

theorem failure_count (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    (failureHeap h r z m).nalloc = h.nalloc + 5 := by
  simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nalloc, rollback_nalloc,
    failureMsgHeap, ZStreamRef.put_nalloc, setD_nalloc, buffers_nalloc,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]

theorem failure_next (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    h.nextBlk ≤ (failureHeap h r z m).nextBlk := by
  have hb := buffers_next (publishedHeap h r z)
  have hn : (publishedHeap h r z).nextBlk = h.nextBlk + 1 := by simp [publishedHeap, stateHeap]
  have he : (failureHeap h r z m).nextBlk = (buffersHeap (publishedHeap h r z)).nextBlk := by
    simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nextBlk, rollback_next,
      failureMsgHeap, setD_nextBlk]
  omega

/-- Failure keeps every old object outside the stream; permission changes
at newly allocated then freed slots are outside the old-object frame. -/
theorem failure_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (m : BPtr) (hf : Fresh h) :
    Frame h (failureHeap h r z m) (StreamRoot r) := by
  let ph := publishedHeap h r z
  let gm := failureMsgHeap h r z m
  have sb := buffers_stable ph
  have sr := rollback_stable ph gm
  refine frame_of_old (g := failureHeap h r z m) r hf ?_ ?_ ?_
    (failure_next h r z m) (by rw [failure_count]; omega) ?_
  · rw [failure_heap_eq]
    change h.static = (r.put (rollbackBuffers ph gm) { failureStream h z m with state := none }).static
    rw [ZStreamRef.put_static, sr.static]
    change h.static = (r.put (setD (buffersHeap ph) h.nextBlk (failureState ph r)) (failureStream h z m)).static
    rw [ZStreamRef.put_static, setD_static, sb.static]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.allocOk = (r.put (rollbackBuffers ph gm) { failureStream h z m with state := none }).allocOk
    rw [ZStreamRef.put_allocOk, sr.allocOk]
    change h.allocOk = (r.put (setD (buffersHeap ph) h.nextBlk (failureState ph r)) (failureStream h z m)).allocOk
    rw [ZStreamRef.put_allocOk, setD_allocOk, sb.allocOk]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.garbage = (r.put (rollbackBuffers ph gm) { failureStream h z m with state := none }).garbage
    rw [ZStreamRef.put_garbage, sr.garbage]
    change h.garbage = (r.put (setD (buffersHeap ph) h.nextBlk (failureState ph r)) (failureStream h z m)).garbage
    rw [ZStreamRef.put_garbage, setD_garbage, sb.garbage]
    simp [ph, publishedHeap, stateHeap]
  · intro x hx hn
    have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
    have hds : x ≠ h.nextBlk := by omega
    have a : SlotSame h ph x :=
      (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
        (slot_stateHeap_old _ (baseState r) x (by simpa using hx))
    have b := a.trans (buffers_old ph x (by omega))
    have c := b.trans (slot_setD_except _ h.nextBlk (failureState ph r) x hds)
    have d : SlotSame h gm x := c.trans (slot_put_except _ r (failureStream h z m) x hn)
    have e := d.trans (rollback_old ph gm x (by omega))
    have f := e.trans (slot_put_except _ r { failureStream h z m with state := none } x hn)
    rw [failure_heap_eq]
    exact f.trans (slot_clearD_except _ h.nextBlk x hds)

/-- Cleanup restores the existence of exactly the original objects.
This is pointwise: internal table capacities may remain enlarged. -/
theorem failure_shape {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hf : Fresh h) (m : BPtr) : Shape h (failureHeap h r z m) := by
  let ph := publishedHeap h r z
  let gf := setD (buffersHeap ph) h.nextBlk (failureState ph r)
  let gm := failureMsgHeap h r z m
  let gr := rollbackBuffers ph gm
  let zc : ZStream := { failureStream h z m with state := none }
  have hfp : Fresh ph := fresh_stateHeap ((shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf) _
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw hz
  have hzM : r.get gm = some (failureStream h z m) := get_failure_message hz m
  have hzR : r.get gr = some (failureStream h z m) := by simpa [gr] using hzM
  have si := shape_put hz (stateStream z h.nextBlk)
  have sm := shape_put hzF (failureStream h z m)
  have se := shape_put hzR zc
  have sb := buffers_stable ph
  have sr := rollback_stable ph gm
  have hd : h.dstates h.nextBlk = none := (Heap.not_live.mp (hf _ (Nat.le_refl _))).2.2.2.2.1
  intro x
  have arrays := rollback_arrays_at (g := gm) hfp x
    (by simp [gm, failureMsgHeap, ph]) (by simp [gm, failureMsgHeap, ph])
  have bytes : (failureHeap h r z m).bytes x = h.bytes x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.1
  have words : (failureHeap h r z m).words x = h.words x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.2
  have dstates : (failureHeap h r z m).dstates x = h.dstates x := by
    rw [failure_heap_eq]
    change upd (r.put gr zc).dstates h.nextBlk none x = h.dstates x
    rw [ZStreamRef.put_dstates, sr.dstates]
    change upd (r.put gf (failureStream h z m)).dstates h.nextBlk none x = h.dstates x
    rw [ZStreamRef.put_dstates]
    simp only [gf, setD, upd_upd, buffers_dstates]
    simp only [ph, publishedHeap, stateHeap_dstates, ZStreamRef.put_dstates,
      ZStreamRef.put_nextBlk, upd_upd, upd_apply]
    by_cases hx : x = h.nextBlk <;> simp [hx, hd]
  refine ⟨congrArg Option.isSome bytes, congrArg Option.isSome words, ?_, ?_,
    congrArg Option.isSome dstates, ?_, ?_⟩
  · rw [failure_heap_eq]
    change ((r.put gr zc).streams x).isSome = (h.streams x).isSome
    rw [(se x).2.2.1, sr.streams]
    change ((r.put gf (failureStream h z m)).streams x).isSome = _
    rw [(sm x).2.2.1]
    change ((buffersHeap ph).streams x).isSome = _
    rw [sb.streams]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.1
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders, sr.gzheaders]
    change ((r.put gf (failureStream h z m)).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders]
    change ((buffersHeap ph).gzheaders x).isSome = _
    rw [sb.gzheaders]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).istates x).isSome = _
    rw [ZStreamRef.put_istates, sr.istates]
    change ((r.put gf (failureStream h z m)).istates x).isSome = _
    rw [ZStreamRef.put_istates]
    change ((buffersHeap ph).istates x).isSome = _
    rw [sb.istates]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzstates x).isSome = (h.gzstates x).isSome
    rw [(se x).2.2.2.2.2.2, sr.gzstates]
    change ((r.put gf (failureStream h z m)).gzstates x).isSome = _
    rw [(sm x).2.2.2.2.2.2]
    change ((buffersHeap ph).gzstates x).isSome = _
    rw [sb.gzstates]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.2.2.2.2

theorem failure_stream_cleared {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (m : BPtr) :
    r.get (failureHeap h r z m) = some { failureStream h z m with state := none } := by
  rw [failure_heap_eq]
  simp only [clearDHeap, ZStreamRef.get_dstates]
  exact ZStreamRef.get_put_same (by simpa using get_failure_message hz m) _

end Zlib.Deflate.Proofs.DefaultInit
