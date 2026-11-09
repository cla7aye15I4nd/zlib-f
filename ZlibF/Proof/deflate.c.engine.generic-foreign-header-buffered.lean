import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-ready-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-buffered-boundary»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual header source retains the initialized empty boundary through
foreign publication and the real partial-output retry-marker store. -/
theorem foreign_zlib_header_buffered {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (status : d.status = INIT_STATE) (wrap : d.wrap = 1) (strategy : d.strategy = 0)
    (window : d.w_bits = 15) (start : d.strstart = 0) (pending : d.pending = 0)
    (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) (next : M Int32) :
    ∃ produced after z' result,
      publicZlibHeader (some r) (some (.tab ds)) next h =
        (if result.pending != 0 then .ok (Z_OK, after) else next after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ produced = min 2 z.avail_out.toNat ∧
      result.pending.toNat + produced = 2 ∧ result.status = BUSY_STATE ∧ result.bi_valid.toInt = 0 ∧
      result.last_flush = (if result.pending != 0 then -1 else d.last_flush) ∧
      result = { d with
        pending := result.pending, pending_out := result.pending_out,
        status := BUSY_STATE, last_flush := result.last_flush } := by
  let ready := levelHeaderReady h r ds pb z d buf
  obtain ⟨stateE, buffersE⟩ := foreign_header_ready_buffered boundary trees buffers pending cursor
  obtain ⟨before, pendingE⟩ := good_pending_bits stateE.good
  obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flush, stateM, buffersM,
      accountM, _sizesM, _storageM, amount, count, fields, _publishM, _bytesM, _pendingM, _wireM, _frameM⟩ :=
    flush_pending_buffered_foreign_boundary stateE buffersE pointer pendingE
  have account : StreamAccounting z zm 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans (stream_accounting_zero z) accountM
  have pendingM : dm.pending.toNat + produced = 2 := count
  have amountM : produced = min 2 z.avail_out.toNat := amount
  have statusM : dm.status = BUSY_STATE := by rw [fields]; rfl
  have bitsM : dm.bi_valid.toInt = 0 := by rw [fields]; exact bits
  have fieldsM : dm = { d with
        pending := dm.pending, pending_out := dm.pending_out,
        status := BUSY_STATE, last_flush := d.last_flush } := by rw [fields]; rfl
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have prepared := generic_zlib_header_prepare_source boundary.good.live.hz boundary.good.live.hs
    status wrap strategy window start pending trees.base.pbuf trees.base.bytes room trees.base.rw next
  by_cases waiting : (dm.pending != 0) = true
  · have stateF := last_flush_buffered_boundary stateM (-1)
    have run : publicZlibHeader (some r) (some (.tab ds)) next h =
        .ok (Z_OK, setD middle ds {dm with last_flush := -1}) := by
      rw [prepared]
      simp only [bind_app, flush, rdD_eq, stateM.good.live.hs, waiting, ite_true, wrD_eq, pure_app]
    refine ⟨produced, _, zm, _, ?_, stateF, last_flush_buffers stateM.good buffersM (-1), account,
      amountM, pendingM, statusM, bitsM, ?_, ?_⟩
    · simpa only [waiting, ite_true] using run
    · simp only [waiting, ite_true]
    · rw [fieldsM]
  · have run : publicZlibHeader (some r) (some (.tab ds)) next h = next middle := by
      rw [prepared]
      simp only [bind_app, flush, rdD_eq, stateM.good.live.hs, waiting, Bool.false_eq_true, ite_false]
    refine ⟨produced, middle, zm, dm, ?_, stateM, buffersM, account,
      amountM, pendingM, statusM, bitsM, ?_, ?_⟩
    · simpa only [waiting, Bool.false_eq_true, ite_false] using run
    · simp only [waiting, Bool.false_eq_true, ite_false]; rw [fieldsM]
    · rw [fieldsM]
end Zlib.Deflate.Engine.Proofs
