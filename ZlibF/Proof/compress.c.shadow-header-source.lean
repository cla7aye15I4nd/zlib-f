import ZlibF.Proof.«compress.c.shadow-header-pending»

/-! # Actual first NO_FLUSH call stopped by a one-byte header offer -/
namespace ZlibF.Spec.Public.Proofs.CompressShadowHeader
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem no_flush_header_entry {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState}
    (live : DLive h (.tab slot) ds z d) (status : d.status = INIT_STATE)
    (pending : d.pending = 0) (last : d.last_flush = -2)
    (one : z.avail_out = 1) (empty : z.avail_in = 0) (output : z.next_out ≠ .null) :
    deflate (some (.tab slot)) Z_NO_FLUSH h =
      publicZlibHeader (some (.tab slot)) (some (.tab ds))
        (publicDataTail (some (.tab slot)) (some (.tab ds)) Z_NO_FLUSH)
        (setD h ds {d with last_flush := Z_NO_FLUSH}) := by
  have checked := stateCheck_live live
  have rank0 : RANK Z_NO_FLUSH = pure 0 := rfl
  have rankOld : RANK (-2) = pure (-4) := rfl
  rw [public_deflate_source]
  simp only [bind_app,pure_app,checked,show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide,
    show (Z_NO_FLUSH < 0) = False from by decide,decide_false,Bool.false_or,
    Bool.false_eq_true,ite_false,zrd_eq,live.hz,live.zst,castDeflateState,
    ldZStream_ok live.hz,ldDeflateState_tab live.hs,empty,
    show ((0 : UInt32) != 0) = false from rfl,Bool.false_and,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr output,
    status,show (INIT_STATE == FINISH_STATE) = false from by decide,
    one,show ((1 : UInt32) == 0) = false from rfl,
    wrD_eq,live.hs,pending,show ((0 : UInt64) != 0) = false from rfl,
    last,rank0,rankOld,show ((0 : Int32) ≤ -4) = False from by decide,
    rdD_eq,setD_dstates_same,ZStreamRef.get_setD]

def oneHeaderHeap (h : Heap) (slot ds pb : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (off : Nat) (output pending : Array UInt8) : Heap :=
  let ready := levelHeaderReady h (.tab slot) ds pb z d pending
  let flushed := oneFlushHeap ready slot ds pb {z with adler := 1} (levelHeaderState d)
    ref off output (levelHeaderBytes d.level pending)
  setD flushed ds {pendingState (levelHeaderState d) (.ref (.blk pb) 1) 1 with last_flush := -1}

theorem header_one_run {h : Heap} {slot ds pb off : Nat} {z : ZStream} {d : DeflateState}
    {ref : BRef} {output pending : Array UInt8}
    (hz : (ZStreamRef.tab slot).get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (status : d.status = INIT_STATE) (wrap : d.wrap = 1)
    (bits : d.bi_valid = 0) (strategy : d.strategy = 0) (window : d.w_bits = 15)
    (start : d.strstart = 0) (count : d.pending = 0)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = d.pending_buf)
    (pendingGet : h.bytes pb = some pending) (room : 2 ≤ pending.size) (pendingRw : h.ro pb = false)
    (one : z.avail_out = 1) (outPtr : z.next_out = .ref ref off)
    (outGet : Space.get h ref = some output) (outRw : Space.ro h ref = false)
    (outBound : off+1 ≤ output.size)
    (notPending : ref ≠ .blk pb) (notState : ref ≠ .dstate_depth ds) (next : M Int32) :
    publicZlibHeader (some (.tab slot)) (some (.tab ds)) next h =
      .ok (Z_OK,oneHeaderHeap h slot ds pb z d ref off output pending) := by
  let ready := levelHeaderReady h (.tab slot) ds pb z d pending
  let queued := levelHeaderState d
  let bytes := levelHeaderBytes d.level pending
  have prep := generic_zlib_header_prepare_source hz hd status wrap strategy window start count
    pendingPtr pendingGet room pendingRw next
  have hzR : (ZStreamRef.tab slot).get ready = some {z with adler := 1} := by
    simp only [ready,levelHeaderReady,ZStreamRef.get_setD]
    exact ZStreamRef.get_put_same (by simpa only [stream_get_bytes] using hz) _
  have hdR : ready.dstates ds = some queued := by simp [ready,levelHeaderReady,queued]
  have getR : ready.bytes pb = some bytes := by simp [ready,levelHeaderReady,bytes]
  have view : Space.get ready ref = some output := by
    have state0 : ({h with bytes := upd h.bytes pb (some bytes)} : Heap).dstates ds = some d := hd
    rw [show ready = setD ((ZStreamRef.tab slot).put {h with bytes := upd h.bytes pb (some bytes)}
      {z with adler := 1}) ds queued from rfl,
      byte_view_setD_depth (by simpa only [ZStreamRef.put_dstates] using state0) rfl,
      byte_get_stream_put]
    exact (Zlib.Inflate.Proofs.byte_view_get_put_ne h notPending bytes).trans outGet
  have roR : Space.ro ready ref = false := by
    cases ref <;> simpa only [Space.ro,ready,levelHeaderReady,setD_ro,ZStreamRef.put_ro] using outRw
  have flushed := flush_one_run hzR state hdR (by exact bits) rfl one outPtr
    (by simpa only [queued,levelHeaderState,cursor] using pendingPtr) view roR getR
    (by simpa only [bytes,levelHeaderBytes,Array.size_set!] using room) outBound notPending notState
  rw [prep]
  simp only [bind_app,flushed,rdD_eq,oneFlushHeap,setD_dstates_same,
    queued,levelHeaderState,pendingState]
  simp only [show ((2 : UInt64)-(1 : UInt32).toUInt64 == 0) = false from by decide,
    show ((2 : UInt64)-(1 : UInt32).toUInt64 != 0) = true from by decide,ite_false,ite_true]
  simp only [wrD_eq,setD_dstates_same,bind_app,pure_app,setD_setD]
  rfl

#print axioms no_flush_header_entry
#print axioms header_one_run
end ZlibF.Spec.Public.Proofs.CompressShadowHeader
