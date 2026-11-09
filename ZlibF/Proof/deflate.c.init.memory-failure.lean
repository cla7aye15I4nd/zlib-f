import ZlibF.Proof.«deflate.c.init.memory-source»
import ZlibF.Proof.«deflate.c.init.failure»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
variable (memory : Nat)

theorem buffers_stable (h : Heap) : StableFields h (buffersHeap h memory) :=
  (((byteResult_stable h 65536).trans (wordResult_stable (windowHeap h) 32768)).trans
    (wordResult_stable (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2))).trans (byteResult_stable (headHeap h memory) (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat))


theorem buffers_next (h : Heap) : h.nextBlk ≤ (buffersHeap h memory).nextBlk := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  have d := byteResult_next (headHeap h memory) (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat)
  dsimp only [buffersHeap, headHeap, prevHeap, windowHeap] at *
  omega

theorem buffers_old (h : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame h (buffersHeap h memory) x := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  exact ((byteResult_old h 65536 x hx).trans
    (wordResult_old (windowHeap h) 32768 x (by dsimp only [windowHeap] at *; omega))).trans
    ((wordResult_old (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2) x (by dsimp only [prevHeap, windowHeap] at *; omega)).trans
      (byteResult_old (headHeap h memory) (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat) x (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega)))

@[simp] theorem buffers_nalloc (h : Heap) : (buffersHeap h memory).nalloc = h.nalloc + 4 := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap, Nat.add_assoc]

@[simp] theorem buffers_dstates (h : Heap) : (buffersHeap h memory).dstates = h.dstates := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

@[simp] theorem get_buffersHeap (h : Heap) (r : ZStreamRef) : r.get (buffersHeap h memory) = r.get h := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

theorem buffers_live (h : Heap) (x : Nat) :
    (buffersHeap h memory).live x ↔ h.live x ∨ (bufferPointers h memory).1 = .ref (.blk x) 0 ∨
      (bufferPointers h memory).2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h memory).2.2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h memory).2.2.2 = .ref (.blk x) 0 := by
  simp only [buffersHeap, byteResult_live, headHeap, wordResult_live, prevHeap,
    windowHeap, bufferPointers, or_assoc]


/-- Every returned buffer is NULL or the live allocation of its request.
The two byte buffers and two word buffers cannot alias when non-NULL. -/
theorem buffers_freeable (h : Heap) :
    FreeableB (buffersHeap h memory) (bufferPointers h memory).1 ∧
    FreeableW (buffersHeap h memory) (bufferPointers h memory).2.1 ∧
    FreeableW (buffersHeap h memory) (bufferPointers h memory).2.2.1 ∧
    FreeableB (buffersHeap h memory) (bufferPointers h memory).2.2.2 ∧
    ((bufferPointers h memory).2.2.2 = .null ∨ (bufferPointers h memory).1 = .null ∨
      (bufferPointers h memory).2.2.2 ≠ (bufferPointers h memory).1) ∧
    ((bufferPointers h memory).2.2.1 = .null ∨ (bufferPointers h memory).2.1 = .null ∨
      (bufferPointers h memory).2.2.1 ≠ (bufferPointers h memory).2.1) := by
  by_cases hw : h.allocOk h.nalloc = true <;>
    by_cases hp : h.allocOk (h.nalloc + 1) = true <;>
    by_cases hq : h.allocOk (h.nalloc + 2) = true <;>
    by_cases hb : h.allocOk (h.nalloc + 3) = true
  all_goals simp [FreeableB, FreeableW, bufferPointers, buffersHeap, headHeap, prevHeap, windowHeap,
    byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap, failedHeap,
    Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

/-- The failure test sees the exact four allocator outcomes. -/
theorem buffers_failed_iff (h : Heap) :
    ((bufferPointers h memory).1 == .null || (bufferPointers h memory).2.1 == .null ||
      (bufferPointers h memory).2.2.1 == .null || (bufferPointers h memory).2.2.2 == .null) = false ↔
      h.allocOk h.nalloc = true ∧ h.allocOk (h.nalloc + 1) = true ∧
        h.allocOk (h.nalloc + 2) = true ∧ h.allocOk (h.nalloc + 3) = true := by
  by_cases hw : h.allocOk h.nalloc = true <;>
    by_cases hp : h.allocOk (h.nalloc + 1) = true <;>
    by_cases hq : h.allocOk (h.nalloc + 2) = true <;>
    by_cases hb : h.allocOk (h.nalloc + 3) = true
  all_goals simp [bufferPointers, buffersHeap, headHeap, prevHeap, windowHeap,
    byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap, failedHeap,
    Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]


def rollbackBuffers (h g : Heap) : Heap :=
  freeBytes (freeWords (freeWords (freeBytes g (bufferPointers h memory).2.2.2)
    (bufferPointers h memory).2.2.1) (bufferPointers h memory).2.1) (bufferPointers h memory).1

theorem rollback_stable (h g : Heap) : StableFields g (rollbackBuffers memory h g) := by
  unfold rollbackBuffers
  exact (((freeBytes_stable g _).trans (freeWords_stable _ _)).trans
    (freeWords_stable _ _)).trans (freeBytes_stable _ _)

@[simp] theorem rollback_nalloc (h g : Heap) : (rollbackBuffers memory h g).nalloc = g.nalloc := by
  simp [rollbackBuffers]

@[simp] theorem rollback_next (h g : Heap) : (rollbackBuffers memory h g).nextBlk = g.nextBlk := by
  simp [rollbackBuffers]

@[simp] theorem get_rollback (h g : Heap) (r : ZStreamRef) : r.get (rollbackBuffers memory h g) = r.get g := by
  simp [rollbackBuffers]

theorem rollback_old (h g : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame g (rollbackBuffers memory h g) x := by
  have a := byteResult_next h 65536
  have b := wordResult_next (windowHeap h) 32768
  have c := wordResult_next (prevHeap h) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  have i1 := slot_freeBytePtr_old (headHeap h memory) g x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i2 := slot_freeWordPtr_old (prevHeap h) (freeBytes g (bytePtr (headHeap h memory))) x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i3 := slot_freeWordPtr_old (windowHeap h)
    (freeWords (freeBytes g (bytePtr (headHeap h memory))) (wordPtr (prevHeap h))) x (by
      dsimp only [windowHeap] at *; omega)
  exact ((i1.trans i2).trans i3).trans (slot_freeBytePtr_old h _ x hx)

/-- Reverse-order cleanup restores every byte/word object lookup for all
sixteen buffer-success patterns. Table capacities may remain enlarged. -/
theorem rollback_arrays_at {h g : Heap} (hf : Fresh h) (x : Nat)
    (hb : g.bytes x = (buffersHeap h memory).bytes x) (hw : g.words x = (buffersHeap h memory).words x) :
    (rollbackBuffers memory h g).bytes x = h.bytes x ∧ (rollbackBuffers memory h g).words x = h.words x := by
  have fW := fresh_byteResult hf 65536
  have fP := fresh_wordResult fW 32768
  have fH := fresh_wordResult fP (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
  have popB := byte_pop_at fH (((UInt32.ofNat (2 ^ (memory + 6))) * 4).toNat) x
  have popH := word_pop_at fP (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2) x
  have popP := word_pop_at fW 32768 x
  have popW := byte_pop_at hf 65536 x
  have b1 : (freeBytes g (bytePtr (headHeap h memory))).bytes x = (headHeap h memory).bytes x := by
    rw [freeBytes_congr_at g (buffersHeap h memory) _ x hb]
    exact popB
  have w1 : (freeBytes g (bytePtr (headHeap h memory))).words x = (headHeap h memory).words x := by
    simpa [buffersHeap] using hw
  have w2 : (freeWords (freeBytes g (bytePtr (headHeap h memory))) (wordPtr (prevHeap h))).words x =
      (prevHeap h).words x := by
    rw [freeWords_congr_at _ (headHeap h memory) _ x w1]
    exact popH
  have w3 : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h memory))) (wordPtr (prevHeap h)))
      (wordPtr (windowHeap h))).words x = (windowHeap h).words x := by
    rw [freeWords_congr_at _ (prevHeap h) _ x w2]
    exact popP
  constructor
  · unfold rollbackBuffers bufferPointers
    simp only [freeWords_bytes] at b1 ⊢
    have eq : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h memory))) (wordPtr (prevHeap h)))
        (wordPtr (windowHeap h))).bytes x = (windowHeap h).bytes x := by
      simpa [headHeap, prevHeap] using b1
    rw [freeBytes_congr_at _ (windowHeap h) _ x eq]
    exact popW
  · unfold rollbackBuffers bufferPointers
    simpa [windowHeap] using w3
def failureState (ph : Heap) (r : ZStreamRef) : DeflateState :=
  { bufferState ph (baseState r memory) memory with status := FINISH_STATE }

def failureStream (h : Heap) (z : ZStream) (m : BPtr) : ZStream :=
  { stateStream z h.nextBlk with msg := m }

def failureMsgHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  let ph := publishedHeap h r z memory
  r.put (setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)) (failureStream h z m)

def failureHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  endHeap (failureMsgHeap memory h r z m) r h.nextBlk (failureStream h z m)
    (failureState memory (publishedHeap h r z memory) r)

theorem failure_heap_eq (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    failureHeap memory h r z m = clearDHeap
      (r.put (rollbackBuffers memory (publishedHeap h r z memory) (failureMsgHeap memory h r z m))
        { failureStream h z m with state := none }) h.nextBlk := by
  unfold failureHeap endHeap clearDHeap
  rw [ZStreamRef.put_dstates, (rollback_stable memory _ _).dstates]
  rfl

theorem get_failure_raw {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) :
    r.get (setD (buffersHeap (publishedHeap h r z memory) memory) h.nextBlk
      (failureState memory (publishedHeap h r z memory) r)) = some (stateStream z h.nextBlk) := by
  simp [publishedHeap, ZStreamRef.get_put_same hz]

theorem get_failure_message {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (m : BPtr) :
    r.get (failureMsgHeap memory h r z m) = some (failureStream h z m) := by
  exact ZStreamRef.get_put_same (get_failure_raw memory hz) _

/-- The actual failed-buffer branch sets FINISH_STATE, obtains the actual
error literal and invokes cleanup on the partially constructed stream. -/
theorem finish_failure {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hd : DefAlloc z) (level : Int32)
    (bad : ((bufferPointers (publishedHeap h r z memory) memory).1 == .null ||
      (bufferPointers (publishedHeap h r z memory) memory).2.1 == .null ||
      (bufferPointers (publishedHeap h r z memory) memory).2.2.1 == .null ||
      (bufferPointers (publishedHeap h r z memory) memory).2.2.2 == .null) = true) :
    ∃ m, finish (some r) (some (.tab h.nextBlk)) level memory (bufferPointers (publishedHeap h r z memory) memory)
        (setD (buffersHeap (publishedHeap h r z memory) memory) h.nextBlk
          (bufferState (publishedHeap h r z memory) (baseState r memory) memory)) =
      .ok (Z_MEM_ERROR, failureHeap memory h r z m) := by
  let ph := publishedHeap h r z memory
  let gf := setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)
  obtain ⟨m, hm⟩ := memory_message gf
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw memory hz
  have hzM := get_failure_message memory hz m
  have hl : DLive (failureMsgHeap memory h r z m) r h.nextBlk (failureStream h z m) (failureState memory ph r) := by
    refine ⟨hzM, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [failureMsgHeap, ph]
    · simp [failureState, GoodStatus]
    · simpa [failureStream, stateStream] using (show z.zalloc ≠ .null by rw [hd.1]; decide)
    · simpa [failureStream, stateStream] using (show z.zfree ≠ .null by rw [hd.2]; decide)
  obtain ⟨hw, hp, hq, hb, hwb, hpq⟩ := buffers_freeable memory ph
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
  change (do let _ ← deflateEnd (some r); pure Z_MEM_ERROR) (failureMsgHeap memory h r z m) = _
  rw [bind_app, release]
  rfl

theorem failure_count (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    (failureHeap memory h r z m).nalloc = h.nalloc + 5 := by
  simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nalloc, rollback_nalloc,
    failureMsgHeap, ZStreamRef.put_nalloc, setD_nalloc, buffers_nalloc,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]

theorem failure_next (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    h.nextBlk ≤ (failureHeap memory h r z m).nextBlk := by
  have hb := buffers_next memory (publishedHeap h r z memory)
  have hn : (publishedHeap h r z memory).nextBlk = h.nextBlk + 1 := by simp [publishedHeap, stateHeap]
  have he : (failureHeap memory h r z m).nextBlk = (buffersHeap (publishedHeap h r z memory) memory).nextBlk := by
    simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nextBlk, rollback_next,
      failureMsgHeap, setD_nextBlk]
  omega

/-- Failure keeps every old object outside the stream; permission changes
at newly allocated then freed slots are outside the old-object frame. -/
theorem failure_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (m : BPtr) (hf : Fresh h) :
    Frame h (failureHeap memory h r z m) (StreamRoot r) := by
  let ph := publishedHeap h r z memory
  let gm := failureMsgHeap memory h r z m
  have sb := buffers_stable memory ph
  have sr := rollback_stable memory ph gm
  refine frame_of_old (g := failureHeap memory h r z m) r hf ?_ ?_ ?_
    (failure_next memory h r z m) (by rw [failure_count]; omega) ?_
  · rw [failure_heap_eq]
    change h.static = (r.put (rollbackBuffers memory ph gm) { failureStream h z m with state := none }).static
    rw [ZStreamRef.put_static, sr.static]
    change h.static = (r.put (setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)) (failureStream h z m)).static
    rw [ZStreamRef.put_static, setD_static, sb.static]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.allocOk = (r.put (rollbackBuffers memory ph gm) { failureStream h z m with state := none }).allocOk
    rw [ZStreamRef.put_allocOk, sr.allocOk]
    change h.allocOk = (r.put (setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)) (failureStream h z m)).allocOk
    rw [ZStreamRef.put_allocOk, setD_allocOk, sb.allocOk]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.garbage = (r.put (rollbackBuffers memory ph gm) { failureStream h z m with state := none }).garbage
    rw [ZStreamRef.put_garbage, sr.garbage]
    change h.garbage = (r.put (setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)) (failureStream h z m)).garbage
    rw [ZStreamRef.put_garbage, setD_garbage, sb.garbage]
    simp [ph, publishedHeap, stateHeap]
  · intro x hx hn
    have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
    have hds : x ≠ h.nextBlk := by omega
    have a : SlotSame h ph x :=
      (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
        (slot_stateHeap_old _ (baseState r memory) x (by simpa using hx))
    have b := a.trans (buffers_old memory ph x (by omega))
    have c := b.trans (slot_setD_except _ h.nextBlk (failureState memory ph r) x hds)
    have d : SlotSame h gm x := c.trans (slot_put_except _ r (failureStream h z m) x hn)
    have e := d.trans (rollback_old memory ph gm x (by omega))
    have f := e.trans (slot_put_except _ r { failureStream h z m with state := none } x hn)
    rw [failure_heap_eq]
    exact f.trans (slot_clearD_except _ h.nextBlk x hds)

/-- Cleanup restores the existence of exactly the original objects.
This is pointwise: internal table capacities may remain enlarged. -/
theorem failure_shape {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hf : Fresh h) (m : BPtr) : Shape h (failureHeap memory h r z m) := by
  let ph := publishedHeap h r z memory
  let gf := setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r)
  let gm := failureMsgHeap memory h r z m
  let gr := rollbackBuffers memory ph gm
  let zc : ZStream := { failureStream h z m with state := none }
  have hfp : Fresh ph := fresh_stateHeap ((shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf) _
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw memory hz
  have hzM : r.get gm = some (failureStream h z m) := get_failure_message memory hz m
  have hzR : r.get gr = some (failureStream h z m) := by simpa [gr] using hzM
  have si := shape_put hz (stateStream z h.nextBlk)
  have sm := shape_put hzF (failureStream h z m)
  have se := shape_put hzR zc
  have sb := buffers_stable memory ph
  have sr := rollback_stable memory ph gm
  have hd : h.dstates h.nextBlk = none := (Heap.not_live.mp (hf _ (Nat.le_refl _))).2.2.2.2.1
  intro x
  have arrays := rollback_arrays_at memory (g := gm) hfp x
    (by simp [gm, failureMsgHeap, ph]) (by simp [gm, failureMsgHeap, ph])
  have bytes : (failureHeap memory h r z m).bytes x = h.bytes x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.1
  have words : (failureHeap memory h r z m).words x = h.words x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.2
  have dstates : (failureHeap memory h r z m).dstates x = h.dstates x := by
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
    change ((buffersHeap ph memory).streams x).isSome = _
    rw [sb.streams]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.1
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders, sr.gzheaders]
    change ((r.put gf (failureStream h z m)).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders]
    change ((buffersHeap ph memory).gzheaders x).isSome = _
    rw [sb.gzheaders]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).istates x).isSome = _
    rw [ZStreamRef.put_istates, sr.istates]
    change ((r.put gf (failureStream h z m)).istates x).isSome = _
    rw [ZStreamRef.put_istates]
    change ((buffersHeap ph memory).istates x).isSome = _
    rw [sb.istates]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzstates x).isSome = (h.gzstates x).isSome
    rw [(se x).2.2.2.2.2.2, sr.gzstates]
    change ((r.put gf (failureStream h z m)).gzstates x).isSome = _
    rw [(sm x).2.2.2.2.2.2]
    change ((buffersHeap ph memory).gzstates x).isSome = _
    rw [sb.gzstates]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.2.2.2.2

theorem failure_stream_cleared {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (m : BPtr) :
    r.get (failureHeap memory h r z m) = some { failureStream h z m with state := none } := by
  rw [failure_heap_eq]
  simp only [clearDHeap, ZStreamRef.get_dstates]
  exact ZStreamRef.get_put_same (by simpa using get_failure_message memory hz m) _

/-- Complete actual public memory-level initialization when any of the
four buffer requests fails. Every nonfailed request still executes. The
actual End call releases the state and all successfully allocated private
buffers, clears the stream state and restores exactly the old live set.
Only the caller stream may differ among pre-existing objects. -/
theorem public_buffer_allocation_failure {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLower : 1 ≤ memory) (memoryUpper : memory ≤ 9)
    (levelLower : 0 ≤ (levelValue level).toInt) (levelUpper : (levelValue level).toInt ≤ 9)
    (stateAllocation : h.allocOk h.nalloc = true)
    (bufferFailure : ∃ j, 1 ≤ j ∧ j < 5 ∧ h.allocOk (h.nalloc + j) = false) :
    ∃ msg,
      let hp := r.put h (preparedStream z)
      let after := failureHeap memory hp r (preparedStream z) msg
      deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h = .ok (Z_MEM_ERROR, after) ∧
      r.get after = some {preparedStream z with state := none, msg := msg} ∧
      Frame h after (StreamRoot r) ∧ Shape h after ∧
      (∀ b, after.live b ↔ h.live b) ∧
      (∀ b, h.nextBlk ≤ b → ¬ after.live b) ∧ after.nalloc = h.nalloc + 5 := by
  let hp := r.put h (preparedStream z)
  let zp := preparedStream z
  let ph := publishedHeap hp r zp memory
  have prepared : Fresh hp := (shape_put stream _).fresh (by simp) fresh
  have current : r.get hp = some zp := ZStreamRef.get_put_same stream _
  have defaultCallbacks : DefAlloc zp := prepared_allocators callbacks
  have bad : ((bufferPointers ph memory).1 == .null || (bufferPointers ph memory).2.1 == .null ||
      (bufferPointers ph memory).2.2.1 == .null || (bufferPointers ph memory).2.2.2 == .null) = true := by
    by_cases result : ((bufferPointers ph memory).1 == .null || (bufferPointers ph memory).2.1 == .null ||
        (bufferPointers ph memory).2.2.1 == .null || (bufferPointers ph memory).2.2.2 == .null) = true
    · exact result
    · have no : ((bufferPointers ph memory).1 == .null || (bufferPointers ph memory).2.1 == .null ||
          (bufferPointers ph memory).2.2.1 == .null || (bufferPointers ph memory).2.2.2 == .null) = false := by
        cases value : ((bufferPointers ph memory).1 == .null || (bufferPointers ph memory).2.1 == .null ||
          (bufferPointers ph memory).2.2.1 == .null || (bufferPointers ph memory).2.2.2 == .null)
        · rfl
        · exact False.elim (result value)
      have all := (buffers_failed_iff memory ph).mp no
      have every : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
        intro j bound
        have choices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases choices with rfl | rfl | rfl | rfl
        · simpa only [Nat.add_zero] using all.1
        · exact all.2.1
        · exact all.2.2.1
        · exact all.2.2.2
      obtain ⟨j, lower, upper, failed⟩ := bufferFailure
      have selected := every (j - 1) (by omega)
      have oracle : ph.allocOk = h.allocOk := by simp [ph, publishedHeap, stateHeap, hp]
      have count : ph.nalloc + (j - 1) = h.nalloc + j := by
        simp only [ph, publishedHeap, stateHeap, ZStreamRef.put_nalloc, hp]
        omega
      rw [oracle, count, failed] at selected
      cases selected
  obtain ⟨msg, cleanup⟩ := finish_failure memory current defaultCallbacks (levelValue level) bad
  have source := public_to_finish fresh stream callbacks versionValue level memory memoryLower memoryUpper
    levelLower levelUpper stateAllocation
  have actual : deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h =
      .ok (Z_MEM_ERROR, failureHeap memory hp r zp msg) := source.trans cleanup
  have shapeP := shape_put stream (preparedStream z)
  have shapeF := failure_shape memory current prepared msg
  have shape := shapeP.trans shapeF
  have frame := frame_trans r (frame_put r (preparedStream z) fresh) (failure_frame memory r zp msg prepared)
  refine ⟨msg, actual, ?_, frame, shape, shape.live, ?_, ?_⟩
  · simpa only [failureStream, stateStream, zp] using failure_stream_cleared memory current msg
  · intro b above live
    exact fresh b above ((shape.live b).mp live)
  · simpa only [hp, ZStreamRef.put_nalloc] using failure_count memory hp r zp msg

/-- The actual cleanup removes exactly the state allocation and the
nonnull buffers of the four requests. A failed request contributes no
allocation identity. All other live objects survive. -/
theorem failure_exact_release {h : Heap} {r : ZStreamRef} {z : ZStream}
    (stream : r.get h = some z) (fresh : Fresh h) (msg : BPtr) :
    let ph := publishedHeap h r z memory
    let born := fun b => b = h.nextBlk ∨
      (bufferPointers ph memory).1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.2.2 = .ref (.blk b) 0
    (∀ b, (failureMsgHeap memory h r z msg).live b ↔ h.live b ∨ born b) ∧
    (∀ b, born b → ¬ h.live b) ∧
    (∀ b, (failureHeap memory h r z msg).live b ↔
      (failureMsgHeap memory h r z msg).live b ∧ ¬ born b) := by
  dsimp only
  let ph := publishedHeap h r z memory
  let born := fun b => b = h.nextBlk ∨
      (bufferPointers ph memory).1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph memory).2.2.2 = .ref (.blk b) 0
  have ledger : ∀ b, (failureMsgHeap memory h r z msg).live b ↔ h.live b ∨ born b := by
    intro b
    have before : ph.live b ↔ h.live b ∨ b = h.nextBlk := by
      dsimp only [ph, publishedHeap]
      rw [stateHeap_live, (shape_put stream (stateStream z h.nextBlk)).live]
      simp
    have current : (buffersHeap ph memory).dstates h.nextBlk = some (baseState r memory) := by
      simp [ph, publishedHeap, stateHeap]
    change (r.put (setD (buffersHeap ph memory) h.nextBlk (failureState memory ph r))
      (failureStream h z msg)).live b ↔ _
    rw [(shape_put (get_failure_raw memory stream) (failureStream h z msg)).live]
    rw [(shape_setD current (failureState memory ph r)).live]
    rw [buffers_live memory ph b, before]
    simp only [born, or_assoc]
  have freshBorn : ∀ b, born b → ¬ h.live b := by
    have byteBirth {g : Heap} {b : Nat} (pointer : bytePtr g = .ref (.blk b) 0) : g.nextBlk = b := by
      unfold bytePtr at pointer
      split at pointer
      · simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using pointer
      · cases pointer
    have wordBirth {g : Heap} {b : Nat} (pointer : wordPtr g = .ref (.blk b) 0) : g.nextBlk = b := by
      unfold wordPtr at pointer
      split at pointer
      · simpa only [Ptr.ref.injEq, WRef.blk.injEq, and_true] using pointer
      · cases pointer
    have pw := byteResult_next ph 65536
    have pp := wordResult_next (windowHeap ph) 32768
    have pq := wordResult_next (prevHeap ph) (((UInt32.ofNat (2 ^ (memory + 7))) * 2).toNat / 2)
    have next : ph.nextBlk = h.nextBlk + 1 := by simp [ph, publishedHeap, stateHeap]
    dsimp only [headHeap, prevHeap, windowHeap] at pw pp pq
    intro b created
    have above : h.nextBlk ≤ b := by
      rcases created with state | win | prev | head | pending
      · omega
      · have eq := byteBirth win
        omega
      · have eq := wordBirth prev
        dsimp only [headHeap, prevHeap, windowHeap] at eq
        omega
      · have eq := wordBirth head
        dsimp only [headHeap, prevHeap, windowHeap] at eq
        omega
      · have eq := byteBirth pending
        dsimp only [headHeap, prevHeap, windowHeap] at eq
        omega
    exact fresh b above
  have closed := (failure_shape memory stream fresh msg).live
  refine ⟨ledger, freshBorn, ?_⟩
  intro b
  constructor
  · intro live
    have old := (closed b).mp live
    exact ⟨(ledger b).mpr (Or.inl old), fun created => freshBorn b created old⟩
  · rintro ⟨live, notBorn⟩
    rcases (ledger b).mp live with old | created
    · exact (closed b).mpr old
    · exact False.elim (notBorn created)

/-- One actual public initialization failure combines execution, cleared
state, the old-object frame and an exact allocation/free ledger. The born
set contains only the real state and nonnull request results. Cleanup
removes precisely that set and keeps every earlier live allocation. -/
theorem public_buffer_failure_cleanup {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLower : 1 ≤ memory) (memoryUpper : memory ≤ 9)
    (levelLower : 0 ≤ (levelValue level).toInt) (levelUpper : (levelValue level).toInt ≤ 9)
    (stateAllocation : h.allocOk h.nalloc = true)
    (bufferFailure : ∃ j, 1 ≤ j ∧ j < 5 ∧ h.allocOk (h.nalloc + j) = false) :
    ∃ msg,
      let hp := r.put h (preparedStream z)
      let ph := publishedHeap hp r (preparedStream z) memory
      let beforeCleanup := failureMsgHeap memory hp r (preparedStream z) msg
      let after := failureHeap memory hp r (preparedStream z) msg
      let born := fun b => b = hp.nextBlk ∨
        (bufferPointers ph memory).1 = .ref (.blk b) 0 ∨
        (bufferPointers ph memory).2.1 = .ref (.blk b) 0 ∨
        (bufferPointers ph memory).2.2.1 = .ref (.blk b) 0 ∨
        (bufferPointers ph memory).2.2.2 = .ref (.blk b) 0
      deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112 h = .ok (Z_MEM_ERROR, after) ∧
      r.get after = some {preparedStream z with state := none, msg := msg} ∧
      Frame h after (StreamRoot r) ∧ Shape h after ∧ after.nalloc = h.nalloc + 5 ∧
      (∀ b, beforeCleanup.live b ↔ h.live b ∨ born b) ∧
      (∀ b, born b → ¬ h.live b) ∧
      (∀ b, after.live b ↔ beforeCleanup.live b ∧ ¬ born b) := by
  obtain ⟨msg, run, cleared, frame, shape, live, noNew, count⟩ :=
    public_buffer_allocation_failure memory fresh stream callbacks versionValue level
      memoryLower memoryUpper levelLower levelUpper stateAllocation bufferFailure
  let hp := r.put h (preparedStream z)
  have shapeP := shape_put stream (preparedStream z)
  have prepared : Fresh hp := shapeP.fresh (by simp) fresh
  have current : r.get hp = some (preparedStream z) := ZStreamRef.get_put_same stream _
  obtain ⟨ledger, newBorn, release⟩ := failure_exact_release memory current prepared msg
  refine ⟨msg, run, cleared, frame, shape, count, ?_, ?_, release⟩
  · intro b
    rw [ledger b, shapeP.live b]
  · intro b created old
    exact newBorn b created ((shapeP.live b).mpr old)

end Zlib.Deflate.Proofs.MemoryInit



#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_stable
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_next
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_old
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_nalloc
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_dstates
#print axioms Zlib.Deflate.Proofs.MemoryInit.get_buffersHeap
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_live
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_freeable
#print axioms Zlib.Deflate.Proofs.MemoryInit.buffers_failed_iff
#print axioms Zlib.Deflate.Proofs.MemoryInit.rollback_stable
#print axioms Zlib.Deflate.Proofs.MemoryInit.rollback_nalloc
#print axioms Zlib.Deflate.Proofs.MemoryInit.rollback_next
#print axioms Zlib.Deflate.Proofs.MemoryInit.get_rollback
#print axioms Zlib.Deflate.Proofs.MemoryInit.rollback_old
#print axioms Zlib.Deflate.Proofs.MemoryInit.rollback_arrays_at
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_heap_eq
#print axioms Zlib.Deflate.Proofs.MemoryInit.get_failure_raw
#print axioms Zlib.Deflate.Proofs.MemoryInit.get_failure_message
#print axioms Zlib.Deflate.Proofs.MemoryInit.finish_failure
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_count
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_next
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_frame
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_shape
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_stream_cleared
#print axioms Zlib.Deflate.Proofs.MemoryInit.public_buffer_allocation_failure
#print axioms Zlib.Deflate.Proofs.MemoryInit.failure_exact_release
#print axioms Zlib.Deflate.Proofs.MemoryInit.public_buffer_failure_cleanup
