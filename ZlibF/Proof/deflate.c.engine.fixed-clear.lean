import ZlibF.Proof.«deflate.c.engine.fixed-block»
import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«deflate.c.engine.block-clear-preserve»

/-! # Actual fixed emission restores the next block's cleared counters -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual static preference also includes the force-fixed strategy.
This dispatch result retains both cases of the source condition. -/
theorem flush_fixed_selected_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (stored : UInt64) (last : Int32)
    (prefer : ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
      (prepared.strategy == Z_FIXED) = true)
    (avoid : ¬ (stored + (4 : UInt64) ≤ ((prepared.static_len + 3 + 7) >>> 3) ∧ source != .null)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) last
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_prepare_source]
  simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs,
    prefer, ite_true, avoid, ite_false, BEq.rfl]

/-- The fixed branch's actual reset restores the BL zero frequencies and
both cost counters. This sibling retains data absent from the earlier
fixed-output contract without changing that theorem's statement. -/
theorem fixed_block_clear_execution {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (last : Bool) :
    ∃ after result,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ BlockInit.BlockClear result := by
  obtain ⟨tagged, headerRun, goodH, treesH, buffersH, _sizesH, _storageH, diffH,
    pendingH, bitsH, cursorH, _outputH⟩ := fixed_header_engine (ob := ob) good trees buffers cursor pending bits last
  obtain ⟨_p, _a, _v, _u, fieldsH⟩ := diffH
  obtain ⟨emittedBuf, emitted, payloadRun, goodE, treesE, buffersE, _sizesE, _storageE,
    _fieldsE, sizeE, pendingE, cursorE, _roomE, _outputE⟩ :=
    fixed_payload_ready_fields (ob := ob) goodH treesH buffersH cursorH
      (by rw [fieldsH]; exact memory) pendingH bitsH
      (by rw [fieldsH]; exact count) (by rw [fieldsH]; exact packed) valid
  obtain ⟨reset, resetRun, goodR, treesR, buffersR, _sizesR, _storageR, _ledgerR, clearR, _resetBits⟩ :=
    init_block_clear_engine (ob := ob) goodE treesE buffersE
  obtain ⟨a1, a2, a3, other, otherRun, _good, _trees, _buffers, _sizes, _storage, resetFields, _ledger, _output⟩ :=
    init_block_engine (ob := ob) goodE treesE buffersE
  have same : other = reset := Zlib.Trees.Proofs.same_record_of_runs otherRun resetRun
  rw [same] at resetFields
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [resetFields, sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  cases last with
  | false =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 0 h = .ok ((), _) at headerRun
    refine ⟨_, reset, ?_, goodR, clearR⟩
    unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, headerRun, payloadRun, resetRun,
      show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 1 h = .ok ((), _) at headerRun
    obtain ⟨next, result, windRun, goodA, _treesA, _buffersA, _sizesA, _storageA, diffA, _rest⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR roomR
    refine ⟨_, result, ?_, goodA, clearR.bits diffA⟩
    unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, headerRun, payloadRun, resetRun,
      show ((1 : Int32) != 0) = true from rfl, ite_true, windRun]

end Zlib.Deflate.Engine.Proofs
