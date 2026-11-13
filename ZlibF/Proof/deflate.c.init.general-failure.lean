import ZlibF.Proof.«deflate.c.init.general-alloc»
import ZlibF.Proof.«deflate.c.init.failure»
import ZlibF.Proof.«deflate.c.init.memory-failure»

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
variable (wrap : Int32) (wb mem : Nat)

theorem buffers_stable (h : Heap) : StableFields h (buffersHeap h wb mem) :=
  (((byteResult_stable h (((UInt32.ofNat (2 ^ wb)) * 2).toNat)).trans (wordResult_stable (windowHeap h wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))).trans
    (wordResult_stable (prevHeap h wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))).trans (byteResult_stable (headHeap h wb mem) (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat))


theorem buffers_next (h : Heap) : h.nextBlk ≤ (buffersHeap h wb mem).nextBlk := by
  have a := byteResult_next h (((UInt32.ofNat (2 ^ wb)) * 2).toNat)
  have b := wordResult_next (windowHeap h wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)
  have c := wordResult_next (prevHeap h wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
  have d := byteResult_next (headHeap h wb mem) (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat)
  dsimp only [buffersHeap, headHeap, prevHeap, windowHeap] at *
  omega

theorem buffers_old (h : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame h (buffersHeap h wb mem) x := by
  have a := byteResult_next h (((UInt32.ofNat (2 ^ wb)) * 2).toNat)
  have b := wordResult_next (windowHeap h wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)
  have c := wordResult_next (prevHeap h wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
  exact ((byteResult_old h (((UInt32.ofNat (2 ^ wb)) * 2).toNat) x hx).trans
    (wordResult_old (windowHeap h wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2) x (by dsimp only [windowHeap] at *; omega))).trans
    ((wordResult_old (prevHeap h wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2) x (by dsimp only [prevHeap, windowHeap] at *; omega)).trans
      (byteResult_old (headHeap h wb mem) (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat) x (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega)))

@[simp] theorem buffers_nalloc (h : Heap) : (buffersHeap h wb mem).nalloc = h.nalloc + 4 := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap, Nat.add_assoc]

@[simp] theorem buffers_dstates (h : Heap) : (buffersHeap h wb mem).dstates = h.dstates := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

@[simp] theorem get_buffersHeap (h : Heap) (r : ZStreamRef) : r.get (buffersHeap h wb mem) = r.get h := by
  simp [buffersHeap, headHeap, prevHeap, windowHeap]

theorem buffers_live (h : Heap) (x : Nat) :
    (buffersHeap h wb mem).live x ↔ h.live x ∨ (bufferPointers h wb mem).1 = .ref (.blk x) 0 ∨
      (bufferPointers h wb mem).2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h wb mem).2.2.1 = .ref (.blk x) 0 ∨
      (bufferPointers h wb mem).2.2.2 = .ref (.blk x) 0 := by
  simp only [buffersHeap, byteResult_live, headHeap, wordResult_live, prevHeap,
    windowHeap, bufferPointers, or_assoc]


/-- Every returned buffer is NULL or the live allocation of its request.
The two byte buffers and two word buffers cannot alias when non-NULL. -/
theorem buffers_freeable (h : Heap) :
    FreeableB (buffersHeap h wb mem) (bufferPointers h wb mem).1 ∧
    FreeableW (buffersHeap h wb mem) (bufferPointers h wb mem).2.1 ∧
    FreeableW (buffersHeap h wb mem) (bufferPointers h wb mem).2.2.1 ∧
    FreeableB (buffersHeap h wb mem) (bufferPointers h wb mem).2.2.2 ∧
    ((bufferPointers h wb mem).2.2.2 = .null ∨ (bufferPointers h wb mem).1 = .null ∨
      (bufferPointers h wb mem).2.2.2 ≠ (bufferPointers h wb mem).1) ∧
    ((bufferPointers h wb mem).2.2.1 = .null ∨ (bufferPointers h wb mem).2.1 = .null ∨
      (bufferPointers h wb mem).2.2.1 ≠ (bufferPointers h wb mem).2.1) := by
  by_cases hw : h.allocOk h.nalloc = true <;>
    by_cases hp : h.allocOk (h.nalloc + 1) = true <;>
    by_cases hq : h.allocOk (h.nalloc + 2) = true <;>
    by_cases hb : h.allocOk (h.nalloc + 3) = true
  all_goals simp [FreeableB, FreeableW, bufferPointers, buffersHeap, headHeap, prevHeap, windowHeap,
    byteResult, wordResult, bytePtr, wordPtr, byteHeap, wordHeap, failedHeap,
    Zlib.Zutil.Proofs.allocHeap, hw, hp, hq, hb, Nat.add_assoc]

/-- The failure test sees the exact four allocator outcomes. -/
theorem buffers_failed_iff (h : Heap) :
    ((bufferPointers h wb mem).1 == .null || (bufferPointers h wb mem).2.1 == .null ||
      (bufferPointers h wb mem).2.2.1 == .null || (bufferPointers h wb mem).2.2.2 == .null) = false ↔
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
  freeBytes (freeWords (freeWords (freeBytes g (bufferPointers h wb mem).2.2.2)
    (bufferPointers h wb mem).2.2.1) (bufferPointers h wb mem).2.1) (bufferPointers h wb mem).1

theorem rollback_stable (h g : Heap) : StableFields g (rollbackBuffers wb mem h g) := by
  unfold rollbackBuffers
  exact (((freeBytes_stable g _).trans (freeWords_stable _ _)).trans
    (freeWords_stable _ _)).trans (freeBytes_stable _ _)

@[simp] theorem rollback_nalloc (h g : Heap) : (rollbackBuffers wb mem h g).nalloc = g.nalloc := by
  simp [rollbackBuffers]

@[simp] theorem rollback_next (h g : Heap) : (rollbackBuffers wb mem h g).nextBlk = g.nextBlk := by
  simp [rollbackBuffers]

@[simp] theorem get_rollback (h g : Heap) (r : ZStreamRef) : r.get (rollbackBuffers wb mem h g) = r.get g := by
  simp [rollbackBuffers]

theorem rollback_old (h g : Heap) (x : Nat) (hx : x < h.nextBlk) : SlotSame g (rollbackBuffers wb mem h g) x := by
  have a := byteResult_next h (((UInt32.ofNat (2 ^ wb)) * 2).toNat)
  have b := wordResult_next (windowHeap h wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)
  have c := wordResult_next (prevHeap h wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
  have i1 := slot_freeBytePtr_old (headHeap h wb mem) g x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i2 := slot_freeWordPtr_old (prevHeap h wb) (freeBytes g (bytePtr (headHeap h wb mem))) x (by
    dsimp only [headHeap, prevHeap, windowHeap] at *; omega)
  have i3 := slot_freeWordPtr_old (windowHeap h wb)
    (freeWords (freeBytes g (bytePtr (headHeap h wb mem))) (wordPtr (prevHeap h wb))) x (by
      dsimp only [windowHeap] at *; omega)
  exact ((i1.trans i2).trans i3).trans (slot_freeBytePtr_old h _ x hx)

/-- Reverse-order cleanup restores every byte/word object lookup for all
sixteen buffer-success patterns. Table capacities may remain enlarged. -/
theorem rollback_arrays_at {h g : Heap} (hf : Fresh h) (x : Nat)
    (hb : g.bytes x = (buffersHeap h wb mem).bytes x) (hw : g.words x = (buffersHeap h wb mem).words x) :
    (rollbackBuffers wb mem h g).bytes x = h.bytes x ∧ (rollbackBuffers wb mem h g).words x = h.words x := by
  have fW := fresh_byteResult hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat)
  have fP := fresh_wordResult fW (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)
  have fH := fresh_wordResult fP (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
  have popB := byte_pop_at fH (((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat) x
  have popH := word_pop_at fP (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2) x
  have popP := word_pop_at fW (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2) x
  have popW := byte_pop_at hf (((UInt32.ofNat (2 ^ wb)) * 2).toNat) x
  have b1 : (freeBytes g (bytePtr (headHeap h wb mem))).bytes x = (headHeap h wb mem).bytes x := by
    rw [freeBytes_congr_at g (buffersHeap h wb mem) _ x hb]
    exact popB
  have w1 : (freeBytes g (bytePtr (headHeap h wb mem))).words x = (headHeap h wb mem).words x := by
    simpa [buffersHeap] using hw
  have w2 : (freeWords (freeBytes g (bytePtr (headHeap h wb mem))) (wordPtr (prevHeap h wb))).words x =
      (prevHeap h wb).words x := by
    rw [freeWords_congr_at _ (headHeap h wb mem) _ x w1]
    exact popH
  have w3 : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h wb mem))) (wordPtr (prevHeap h wb)))
      (wordPtr (windowHeap h wb))).words x = (windowHeap h wb).words x := by
    rw [freeWords_congr_at _ (prevHeap h wb) _ x w2]
    exact popP
  constructor
  · unfold rollbackBuffers bufferPointers
    simp only [freeWords_bytes] at b1 ⊢
    have eq : (freeWords (freeWords (freeBytes g (bytePtr (headHeap h wb mem))) (wordPtr (prevHeap h wb)))
        (wordPtr (windowHeap h wb))).bytes x = (windowHeap h wb).bytes x := by
      simpa [headHeap, prevHeap] using b1
    rw [freeBytes_congr_at _ (windowHeap h wb) _ x eq]
    exact popW
  · unfold rollbackBuffers bufferPointers
    simpa [windowHeap] using w3
def failureState (ph : Heap) (r : ZStreamRef) : DeflateState :=
  { bufferState ph (baseState r wrap wb mem) wb mem with status := FINISH_STATE }

def failureStream (h : Heap) (z : ZStream) (m : BPtr) : ZStream :=
  { stateStream z h.nextBlk with msg := m }

def failureMsgHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  let ph := publishedHeap h r z wrap wb mem
  r.put (setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)) (failureStream h z m)

def failureHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) : Heap :=
  endHeap (failureMsgHeap wrap wb mem h r z m) r h.nextBlk (failureStream h z m)
    (failureState wrap wb mem (publishedHeap h r z wrap wb mem) r)

theorem failure_heap_eq (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    failureHeap wrap wb mem h r z m = clearDHeap
      (r.put (rollbackBuffers wb mem (publishedHeap h r z wrap wb mem) (failureMsgHeap wrap wb mem h r z m))
        { failureStream h z m with state := none }) h.nextBlk := by
  unfold failureHeap endHeap clearDHeap
  rw [ZStreamRef.put_dstates, (rollback_stable wb mem _ _).dstates]
  rfl

theorem get_failure_raw {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) :
    r.get (setD (buffersHeap (publishedHeap h r z wrap wb mem) wb mem) h.nextBlk
      (failureState wrap wb mem (publishedHeap h r z wrap wb mem) r)) = some (stateStream z h.nextBlk) := by
  simp [publishedHeap, ZStreamRef.get_put_same hz]

theorem get_failure_message {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (m : BPtr) :
    r.get (failureMsgHeap wrap wb mem h r z m) = some (failureStream h z m) := by
  exact ZStreamRef.get_put_same (get_failure_raw wrap wb mem hz) _

/-- The actual failed-buffer branch sets FINISH_STATE, obtains the actual
error literal and invokes cleanup on the partially constructed stream. -/
theorem finish_failure {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hd : DefAlloc z) (level strategy method : Int32)
    (bad : ((bufferPointers (publishedHeap h r z wrap wb mem) wb mem).1 == .null ||
      (bufferPointers (publishedHeap h r z wrap wb mem) wb mem).2.1 == .null ||
      (bufferPointers (publishedHeap h r z wrap wb mem) wb mem).2.2.1 == .null ||
      (bufferPointers (publishedHeap h r z wrap wb mem) wb mem).2.2.2 == .null) = true) :
    ∃ m, finish (some r) (some (.tab h.nextBlk)) level strategy method mem (bufferPointers (publishedHeap h r z wrap wb mem) wb mem)
        (setD (buffersHeap (publishedHeap h r z wrap wb mem) wb mem) h.nextBlk
          (bufferState (publishedHeap h r z wrap wb mem) (baseState r wrap wb mem) wb mem)) =
      .ok (Z_MEM_ERROR, failureHeap wrap wb mem h r z m) := by
  let ph := publishedHeap h r z wrap wb mem
  let gf := setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)
  obtain ⟨m, hm⟩ := memory_message gf
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw wrap wb mem hz
  have hzM := get_failure_message wrap wb mem hz m
  have hl : DLive (failureMsgHeap wrap wb mem h r z m) r h.nextBlk (failureStream h z m) (failureState wrap wb mem ph r) := by
    refine ⟨hzM, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [failureMsgHeap, ph]
    · simp [failureState, GoodStatus]
    · simpa [failureStream, stateStream] using (show z.zalloc ≠ .null by rw [hd.1]; decide)
    · simpa [failureStream, stateStream] using (show z.zfree ≠ .null by rw [hd.2]; decide)
  obtain ⟨hw, hp, hq, hb, hwb, hpq⟩ := buffers_freeable wb mem ph
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
  change (do let _ ← deflateEnd (some r); pure Z_MEM_ERROR) (failureMsgHeap wrap wb mem h r z m) = _
  rw [bind_app, release]
  rfl

theorem failure_count (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    (failureHeap wrap wb mem h r z m).nalloc = h.nalloc + 5 := by
  simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nalloc, rollback_nalloc,
    failureMsgHeap, ZStreamRef.put_nalloc, setD_nalloc, buffers_nalloc,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]

theorem failure_next (h : Heap) (r : ZStreamRef) (z : ZStream) (m : BPtr) :
    h.nextBlk ≤ (failureHeap wrap wb mem h r z m).nextBlk := by
  have hb := buffers_next wb mem (publishedHeap h r z wrap wb mem)
  have hn : (publishedHeap h r z wrap wb mem).nextBlk = h.nextBlk + 1 := by simp [publishedHeap, stateHeap]
  have he : (failureHeap wrap wb mem h r z m).nextBlk = (buffersHeap (publishedHeap h r z wrap wb mem) wb mem).nextBlk := by
    simp only [failure_heap_eq, clearDHeap, ZStreamRef.put_nextBlk, rollback_next,
      failureMsgHeap, setD_nextBlk]
  omega

/-- Failure keeps every old object outside the stream; permission changes
at newly allocated then freed slots are outside the old-object frame. -/
theorem failure_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (m : BPtr) (hf : Fresh h) :
    Frame h (failureHeap wrap wb mem h r z m) (StreamRoot r) := by
  let ph := publishedHeap h r z wrap wb mem
  let gm := failureMsgHeap wrap wb mem h r z m
  have sb := buffers_stable wb mem ph
  have sr := rollback_stable wb mem ph gm
  refine frame_of_old (g := failureHeap wrap wb mem h r z m) r hf ?_ ?_ ?_
    (failure_next wrap wb mem h r z m) (by rw [failure_count]; omega) ?_
  · rw [failure_heap_eq]
    change h.static = (r.put (rollbackBuffers wb mem ph gm) { failureStream h z m with state := none }).static
    rw [ZStreamRef.put_static, sr.static]
    change h.static = (r.put (setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)) (failureStream h z m)).static
    rw [ZStreamRef.put_static, setD_static, sb.static]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.allocOk = (r.put (rollbackBuffers wb mem ph gm) { failureStream h z m with state := none }).allocOk
    rw [ZStreamRef.put_allocOk, sr.allocOk]
    change h.allocOk = (r.put (setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)) (failureStream h z m)).allocOk
    rw [ZStreamRef.put_allocOk, setD_allocOk, sb.allocOk]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change h.garbage = (r.put (rollbackBuffers wb mem ph gm) { failureStream h z m with state := none }).garbage
    rw [ZStreamRef.put_garbage, sr.garbage]
    change h.garbage = (r.put (setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)) (failureStream h z m)).garbage
    rw [ZStreamRef.put_garbage, setD_garbage, sb.garbage]
    simp [ph, publishedHeap, stateHeap]
  · intro x hx hn
    have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
    have hds : x ≠ h.nextBlk := by omega
    have a : SlotSame h ph x :=
      (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
        (slot_stateHeap_old _ (baseState r wrap wb mem) x (by simpa using hx))
    have b := a.trans (buffers_old wb mem ph x (by omega))
    have c := b.trans (slot_setD_except _ h.nextBlk (failureState wrap wb mem ph r) x hds)
    have d : SlotSame h gm x := c.trans (slot_put_except _ r (failureStream h z m) x hn)
    have e := d.trans (rollback_old wb mem ph gm x (by omega))
    have f := e.trans (slot_put_except _ r { failureStream h z m with state := none } x hn)
    rw [failure_heap_eq]
    exact f.trans (slot_clearD_except _ h.nextBlk x hds)

/-- Cleanup restores the existence of exactly the original objects.
This is pointwise: internal table capacities may remain enlarged. -/
theorem failure_shape {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (hf : Fresh h) (m : BPtr) : Shape h (failureHeap wrap wb mem h r z m) := by
  let ph := publishedHeap h r z wrap wb mem
  let gf := setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r)
  let gm := failureMsgHeap wrap wb mem h r z m
  let gr := rollbackBuffers wb mem ph gm
  let zc : ZStream := { failureStream h z m with state := none }
  have hfp : Fresh ph := fresh_stateHeap ((shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf) _
  have hzF : r.get gf = some (stateStream z h.nextBlk) := get_failure_raw wrap wb mem hz
  have hzM : r.get gm = some (failureStream h z m) := get_failure_message wrap wb mem hz m
  have hzR : r.get gr = some (failureStream h z m) := by simpa [gr] using hzM
  have si := shape_put hz (stateStream z h.nextBlk)
  have sm := shape_put hzF (failureStream h z m)
  have se := shape_put hzR zc
  have sb := buffers_stable wb mem ph
  have sr := rollback_stable wb mem ph gm
  have hd : h.dstates h.nextBlk = none := (Heap.not_live.mp (hf _ (Nat.le_refl _))).2.2.2.2.1
  intro x
  have arrays := rollback_arrays_at wb mem (g := gm) hfp x
    (by simp [gm, failureMsgHeap, ph]) (by simp [gm, failureMsgHeap, ph])
  have bytes : (failureHeap wrap wb mem h r z m).bytes x = h.bytes x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.1
  have words : (failureHeap wrap wb mem h r z m).words x = h.words x := by
    rw [failure_heap_eq]
    simpa [clearDHeap, ph, publishedHeap, stateHeap, gr] using arrays.2
  have dstates : (failureHeap wrap wb mem h r z m).dstates x = h.dstates x := by
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
    change ((buffersHeap ph wb mem).streams x).isSome = _
    rw [sb.streams]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.1
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders, sr.gzheaders]
    change ((r.put gf (failureStream h z m)).gzheaders x).isSome = _
    rw [ZStreamRef.put_gzheaders]
    change ((buffersHeap ph wb mem).gzheaders x).isSome = _
    rw [sb.gzheaders]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).istates x).isSome = _
    rw [ZStreamRef.put_istates, sr.istates]
    change ((r.put gf (failureStream h z m)).istates x).isSome = _
    rw [ZStreamRef.put_istates]
    change ((buffersHeap ph wb mem).istates x).isSome = _
    rw [sb.istates]
    simp [ph, publishedHeap, stateHeap]
  · rw [failure_heap_eq]
    change ((r.put gr zc).gzstates x).isSome = (h.gzstates x).isSome
    rw [(se x).2.2.2.2.2.2, sr.gzstates]
    change ((r.put gf (failureStream h z m)).gzstates x).isSome = _
    rw [(sm x).2.2.2.2.2.2]
    change ((buffersHeap ph wb mem).gzstates x).isSome = _
    rw [sb.gzstates]
    simpa [ph, publishedHeap, stateHeap] using (si x).2.2.2.2.2.2

theorem failure_stream_cleared {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (m : BPtr) :
    r.get (failureHeap wrap wb mem h r z m) = some { failureStream h z m with state := none } := by
  rw [failure_heap_eq]
  simp only [clearDHeap, ZStreamRef.get_dstates]
  exact ZStreamRef.get_put_same (by simpa using get_failure_message wrap wb mem hz m) _

/-- The actual cleanup removes exactly the state allocation and the
nonnull buffers of the four requests. A failed request contributes no
allocation identity. All other live objects survive. -/
theorem failure_exact_release {h : Heap} {r : ZStreamRef} {z : ZStream}
    (stream : r.get h = some z) (fresh : Fresh h) (msg : BPtr) :
    let ph := publishedHeap h r z wrap wb mem
    let born := fun b => b = h.nextBlk ∨
      (bufferPointers ph wb mem).1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.2.2 = .ref (.blk b) 0
    (∀ b, (failureMsgHeap wrap wb mem h r z msg).live b ↔ h.live b ∨ born b) ∧
    (∀ b, born b → ¬ h.live b) ∧
    (∀ b, (failureHeap wrap wb mem h r z msg).live b ↔
      (failureMsgHeap wrap wb mem h r z msg).live b ∧ ¬ born b) := by
  dsimp only
  let ph := publishedHeap h r z wrap wb mem
  let born := fun b => b = h.nextBlk ∨
      (bufferPointers ph wb mem).1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.2.1 = .ref (.blk b) 0 ∨
      (bufferPointers ph wb mem).2.2.2 = .ref (.blk b) 0
  have ledger : ∀ b, (failureMsgHeap wrap wb mem h r z msg).live b ↔ h.live b ∨ born b := by
    intro b
    have before : ph.live b ↔ h.live b ∨ b = h.nextBlk := by
      dsimp only [ph, publishedHeap]
      rw [stateHeap_live, (shape_put stream (stateStream z h.nextBlk)).live]
      simp
    have current : (buffersHeap ph wb mem).dstates h.nextBlk = some (baseState r wrap wb mem) := by
      simp [ph, publishedHeap, stateHeap]
    change (r.put (setD (buffersHeap ph wb mem) h.nextBlk (failureState wrap wb mem ph r))
      (failureStream h z msg)).live b ↔ _
    rw [(shape_put (get_failure_raw wrap wb mem stream) (failureStream h z msg)).live]
    rw [(shape_setD current (failureState wrap wb mem ph r)).live]
    rw [buffers_live wb mem ph b, before]
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
    have pw := byteResult_next ph (((UInt32.ofNat (2 ^ wb)) * 2).toNat)
    have pp := wordResult_next (windowHeap ph wb) (((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2)
    have pq := wordResult_next (prevHeap ph wb) (((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2)
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
  have closed := (failure_shape wrap wb mem stream fresh msg).live
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

