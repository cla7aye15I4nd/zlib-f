import ZlibF.Proof.«deflate.c.init.general»
import ZlibF.Proof.«deflate.c.init.memory-source»

/-! # deflate.c: the allocation of `deflateInit2_` for every parameter tuple

The generalization of `deflate.c.init.memory-source` from window bits 15, the zlib wrapper,
strategy 0 and method 8 to every accepted tuple: the state allocation, its failure, the four
buffer requests (each executes even after an earlier failure) and the cut point before the
cleanup or reset decision.
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The four buffer requests and their intervening stores. -/
def buffers (strm : ZStreamPtr) (s : DeflateStatePtr) (wb mem : Nat) : M (BPtr × WPtr × WPtr × BPtr) := do
  let window ← ZALLOC_bytes strm (UInt32.ofNat (2 ^ wb)) 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm (UInt32.ofNat (2 ^ wb))
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm (UInt32.ofNat (2 ^ (mem + 7)))
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (mem + 6)) })
  let pending_buf ← ZALLOC_bytes strm (UInt32.ofNat (2 ^ (mem + 6))) 4
  wr s (fun d => { d with pending_buf, pending_buf_size := (UInt32.ofNat (2 ^ (mem + 6))).toUInt64 * 4 })
  pure (window, prev, head, pending_buf)

def windowHeap (h : Heap) (wb : Nat) : Heap := byteResult h ((((UInt32.ofNat (2 ^ wb)) * 2).toNat))
def prevHeap (h : Heap) (wb : Nat) : Heap := wordResult (windowHeap h wb) ((((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
def headHeap (h : Heap) (wb mem : Nat) : Heap := wordResult (prevHeap h wb) ((((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))
def buffersHeap (h : Heap) (wb mem : Nat) : Heap := byteResult (headHeap h wb mem) ((((UInt32.ofNat (2 ^ (mem + 6))) * 4).toNat))

def bufferPointers (h : Heap) (wb mem : Nat) : BPtr × WPtr × WPtr × BPtr :=
  (bytePtr h, wordPtr (windowHeap h wb), wordPtr (prevHeap h wb), bytePtr (headHeap h wb mem))

def bufferState (h : Heap) (d : DeflateState) (wb mem : Nat) : DeflateState :=
  { d with
    window := bytePtr h, prev := wordPtr (windowHeap h wb), head := wordPtr (prevHeap h wb),
    high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (mem + 6)),
    pending_buf := bytePtr (headHeap h wb mem),
    pending_buf_size := (UInt32.ofNat (2 ^ (mem + 6))).toUInt64 * 4 }

/-- Each of the four buffer requests executes even if an earlier one fails. -/
theorem buffers_run {h : Heap} {r : ZStreamRef} {z : ZStream} {ds : Nat} {d : DeflateState}
    (wb mem : Nat) (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hs : h.dstates ds = some d) (hds : ds < h.nextBlk) :
    buffers (some r) (some (.tab ds)) wb mem h =
      .ok (bufferPointers h wb mem, setD (buffersHeap h wb mem) ds (bufferState h d wb mem)) := by
  let d1 := { d with window := bytePtr h }
  let H1 := setD (windowHeap h wb) ds d1
  let d2 := { d1 with prev := wordPtr (windowHeap h wb) }
  let H2 := setD (prevHeap h wb) ds d2
  let d3 := { d2 with head := wordPtr (prevHeap h wb) }
  let d4 := { d3 with high_water := 0, lit_bufsize := UInt32.ofNat (2 ^ (mem + 6)) }
  let H4 := setD (headHeap h wb mem) ds d4
  have fW := fresh_byteResult hf ((((UInt32.ofNat (2 ^ wb)) * 2).toNat))
  have fP := fresh_wordResult fW ((((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
  have fH := fresh_wordResult fP ((((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))
  have pW := byteResult_next h ((((UInt32.ofNat (2 ^ wb)) * 2).toNat))
  have pP := wordResult_next (windowHeap h wb) ((((UInt32.ofNat (2 ^ wb)) * 2).toNat / 2))
  have pH := wordResult_next (prevHeap h wb) ((((UInt32.ofNat (2 ^ (mem + 7))) * 2).toNat / 2))
  have hf1 : Fresh H1 := fresh_setD_below fW ds (by dsimp only [windowHeap] at *; omega) d1
  have hf2 : Fresh H2 := fresh_setD_below fP ds (by dsimp only [prevHeap, windowHeap] at *; omega) d2
  have hf4 : Fresh H4 := fresh_setD_below fH ds
    (by dsimp only [headHeap, prevHeap, windowHeap] at *; omega) d4
  have runW := bytes_run hf hz ha (UInt32.ofNat (2 ^ wb)) 2
  have runP := words_run hf1 (r := r) (z := z) (by simpa [H1, windowHeap] using hz) ha (UInt32.ofNat (2 ^ wb))
  have runH := words_run hf2 (r := r) (z := z) (by simpa [H2, prevHeap, windowHeap] using hz) ha
    (UInt32.ofNat (2 ^ (mem + 7)))
  have runB := bytes_run hf4 (r := r) (z := z) (by simpa [H4, headHeap, prevHeap, windowHeap] using hz) ha
    (UInt32.ofNat (2 ^ (mem + 6))) 4
  change ZALLOC_bytes (some r) (UInt32.ofNat (2 ^ wb)) 2 h = .ok (bytePtr h, windowHeap h wb) at runW
  simp only [H1, H2, H4, prevHeap, headHeap, buffersHeap, windowHeap, wordPtr_setD,
    bytePtr_setD, wordResult_setD, byteResult_setD]
    at runP runH runB
  dsimp only [d1, d2, d3, d4, prevHeap, headHeap, windowHeap] at runP runH runB
  unfold buffers
  rw [bind_app, runW]
  simp only [bind_app, wrD_eq, windowHeap, byteResult_dstates, hs, d1, d2, d3, d4]
  rw [runP]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3, d4]
  rw [runH]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3, d4]
  rw [runB]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, pure_app]
  rfl

/-- The state fields written before the four buffer allocations. -/
def baseState (r : ZStreamRef) (wrap : Int32) (wb mem : Nat) : DeflateState :=
  { DeflateState.zeroed with
    strm := some r, status := INIT_STATE, wrap := wrap,
    w_bits := UInt32.ofNat wb, w_size := UInt32.ofNat (2 ^ wb), w_mask := UInt32.ofNat (2 ^ wb) - 1,
    hash_bits := UInt32.ofNat (mem + 7), hash_size := UInt32.ofNat (2 ^ (mem + 7)),
    hash_mask := UInt32.ofNat (2 ^ (mem + 7)) - 1, hash_shift := (UInt32.ofNat (mem + 7) + 2) / 3 }

def stateStream (z : ZStream) (ds : Nat) : ZStream := { z with state := some (.deflate ds) }

def publishedHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (wrap : Int32) (wb mem : Nat) : Heap :=
  stateHeap (r.put h (stateStream z h.nextBlk)) (baseState r wrap wb mem)

/-- The final decision after all four buffer requests. -/
def finish (strm : ZStreamPtr) (s : DeflateStatePtr) (level strategy method : Int32) (mem : Nat)
    (ps : BPtr × WPtr × WPtr × BPtr) : M Int32 := do
  let (window, prev, head, pending_buf) := ps
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf (2 ^ (mem + 6))
  wr s (fun d => { d with sym_buf, sym_end := (UInt32.ofNat (2 ^ (mem + 6)) - 1) * 3 })
  wr s (fun d => { d with level, strategy, «method» := method.toUInt32.toUInt8 })
  deflateReset strm

/-- Naming allocation and cleanup cut points preserves the source. -/
theorem alloc_eq (strm : ZStreamPtr) (level wrap : Int32) (wb mem : Nat) (method strategy : Int32) :
    alloc strm level wrap wb mem method strategy = (do
      zalloc_default strm
      let s ← allocDeflateState
      if s == none then return Z_MEM_ERROR
      stDeflateState s DeflateState.zeroed
      zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
      wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap := wrap,
                              w_bits := UInt32.ofNat wb, w_size := UInt32.ofNat (2 ^ wb),
                              w_mask := UInt32.ofNat (2 ^ wb) - 1, hash_bits := UInt32.ofNat (mem + 7),
                              hash_size := UInt32.ofNat (2 ^ (mem + 7)),
                              hash_mask := UInt32.ofNat (2 ^ (mem + 7)) - 1,
                              hash_shift := (UInt32.ofNat (mem + 7) + 2) / 3 })
      let ps ← buffers strm s wb mem
      finish strm s level strategy method mem ps) := by
  unfold alloc buffers finish
  simp only [M_bind_assoc, M_pure_bind]

/-- State allocation, zeroing and publication, then all four buffer requests: the cut point
before cleanup or reset, for every allocation oracle. -/
theorem alloc_to_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (ho : h.allocOk h.nalloc = true) (level wrap : Int32) (wb mem : Nat) (method strategy : Int32) :
    alloc (some r) level wrap wb mem method strategy h =
      finish (some r) (some (.tab h.nextBlk)) level strategy method mem
        (bufferPointers (publishedHeap h r z wrap wb mem) wb mem)
        (setD (buffersHeap (publishedHeap h r z wrap wb mem) wb mem) h.nextBlk
          (bufferState (publishedHeap h r z wrap wb mem) (baseState r wrap wb mem) wb mem)) := by
  have hfP : Fresh (publishedHeap h r z wrap wb mem) :=
    fresh_stateHeap ((shape_put hz _).fresh (by simp) hf) _
  have hsP : (publishedHeap h r z wrap wb mem).dstates h.nextBlk = some (baseState r wrap wb mem) := by
    simp [publishedHeap, stateHeap]
  have hzP : r.get (publishedHeap h r z wrap wb mem) = some (stateStream z h.nextBlk) := by
    simp [publishedHeap, ZStreamRef.get_put_same hz]
  have hbuffer := buffers_run wb mem hfP hzP (by simpa [stateStream] using ha) hsP
    (by simp [publishedHeap, stateHeap])
  rw [alloc_eq]
  rw [bind_app, allocator_run hz ha]
  simp only []
  have runS : allocDeflateState h = .ok (some (.tab h.nextBlk),
      stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) := allocDeflateState_some ho
  rw [bind_app, runS]
  simp [bind_app, stD_eq, pure_app, ZStreamRef.put_dstates, stateHeap_dstates_same,
    zwr_eq, get_stateHeap, ZStreamRef.get_put_same hz, wrD_eq, upd_upd,
    put_stateHeap, stateHeap_setD, hz, StateRef.ofDeflateState]
  have remaining : (do
      let ps ← buffers (some r) (some (.tab h.nextBlk)) wb mem
      finish (some r) (some (.tab h.nextBlk)) level strategy method mem ps) (publishedHeap h r z wrap wb mem) =
      finish (some r) (some (.tab h.nextBlk)) level strategy method mem
        (bufferPointers (publishedHeap h r z wrap wb mem) wb mem)
        (setD (buffersHeap (publishedHeap h r z wrap wb mem) wb mem) h.nextBlk
          (bufferState (publishedHeap h r z wrap wb mem) (baseState r wrap wb mem) wb mem)) := by
    rw [bind_app, hbuffer]
  simpa only [bind_app, publishedHeap, baseState, stateStream, UInt32.ofNat_add,
    show UInt32.ofNat 7 = (7 : UInt32) from rfl] using remaining

/-- Failure of the state allocation returns before any state is published. -/
theorem alloc_state_fail {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (ha : z.zalloc = .fn "zcalloc")
    (hf : h.allocOk h.nalloc = false) (level wrap : Int32) (wb mem : Nat) (method strategy : Int32) :
    alloc (some r) level wrap wb mem method strategy h =
      .ok (Z_MEM_ERROR, { h with nalloc := h.nalloc + 1 }) := by
  unfold alloc
  rw [bind_app, allocator_run hz ha]
  simp only []
  rw [bind_app, allocDeflateState_none (by rw [hf]; decide)]
  rfl

end Zlib.Deflate.Proofs.GeneralInit
