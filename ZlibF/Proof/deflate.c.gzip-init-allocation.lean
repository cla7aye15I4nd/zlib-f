import ZlibF.Proof.«deflate.c.gzip-init-source»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Actual gzip state record before its four buffer allocation requests. -/
def baseState (r : ZStreamRef) : DeflateState :=
  { DeflateState.zeroed with
    strm := some r, status := INIT_STATE, wrap := 2,
    w_bits := 15, w_size := 32768, w_mask := 32767,
    hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 }

def publishedHeap (h : Heap) (r : ZStreamRef) (z : ZStream) : Heap :=
  stateHeap (r.put h (stateStream z h.nextBlk)) (baseState r)


/-- Exact gzip allocation cut retaining all cleanup/reset calls. -/
theorem allocate_eq (strm : ZStreamPtr) (level : Int32) : allocate strm level = (do
    zalloc_default strm
    let s ← allocDeflateState
    if s == none then return Z_MEM_ERROR
    stDeflateState s DeflateState.zeroed
    zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
    wr s (fun d => { d with
      strm := strm, status := INIT_STATE, wrap := 2,
      w_bits := 15, w_size := 32768, w_mask := 32767,
      hash_bits := 15, hash_size := 32768, hash_mask := 32767, hash_shift := 5 })
    let ps ← buffers strm s
    finish strm s level ps) := by
  unfold allocate buffers finish
  simp only [M_bind_assoc, M_pure_bind]

/-- Actual state allocation, zeroing and publication, followed by all four
buffer requests. Its result is the real cleanup/success cut point for
every four-buffer allocation oracle. -/
theorem allocate_to_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (ho : h.allocOk h.nalloc = true) (level : Int32) :
    allocate (some r) level h =
      finish (some r) (some (.tab h.nextBlk)) level (bufferPointers (publishedHeap h r z))
        (setD (buffersHeap (publishedHeap h r z)) h.nextBlk
          (bufferState (publishedHeap h r z) (baseState r))) := by
  have hfP : Fresh (publishedHeap h r z) :=
    fresh_stateHeap ((shape_put hz _).fresh (by simp) hf) _
  have hsP : (publishedHeap h r z).dstates h.nextBlk = some (baseState r) := by
    simp [publishedHeap, stateHeap]
  have hzP : r.get (publishedHeap h r z) = some (stateStream z h.nextBlk) := by
    simp [publishedHeap, ZStreamRef.get_put_same hz]
  have hbuffer := buffers_run hfP hzP (by simpa [stateStream] using ha) hsP
    (by simp [publishedHeap, stateHeap])
  rw [allocate_eq]
  rw [bind_app, allocator_run hz ha]
  simp only []
  have runS : allocDeflateState h = .ok (some (.tab h.nextBlk),
      stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) := allocDeflateState_some ho
  rw [bind_app, runS]
  simp [bind_app, stD_eq, pure_app, ZStreamRef.put_dstates, stateHeap_dstates_same,
    zwr_eq, get_stateHeap, ZStreamRef.get_put_same hz, wrD_eq, upd_upd,
    put_stateHeap, stateHeap_setD, hz, StateRef.ofDeflateState]
  change (do let ps ← buffers (some r) (some (.tab h.nextBlk))
             finish (some r) (some (.tab h.nextBlk)) level ps) (publishedHeap h r z) = _
  rw [bind_app, hbuffer]

end Zlib.Deflate.Proofs.DefaultGzipInit
