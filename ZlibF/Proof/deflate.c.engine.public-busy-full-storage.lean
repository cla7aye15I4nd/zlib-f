import ZlibF.Proof.«deflate.c.engine.public-data-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-busy-counters»
/-! # Full object and allocation frames for both public data paths -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual pending-first public exhaustion retains its complete object/allocation frame. -/
theorem public_pending_exhausted_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool} {flush rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨pb, other, _z', _result, _written, _remaining, base, tested, _goodA, _buffersA, _account,
      _sizes, storage, _rest⟩ := public_pending_exhausted_allowed flush good buffers pointer input flagLo flagHi
        status positive enough low pending
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact ⟨storage.shape, storage.private_frame base, full_shape_live_change storage.shape,
    storage.nalloc, storage.nextBlk⟩

/-- Complete BUSY FINISH calls compose old pending output, real strategy and trailer totals. -/
theorem public_busy_finish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  have shape0 := shape_setD boundary.good.live.hs { d with last_flush := Z_FINISH }
  have frame0 : Frame h (setD h ds { d with last_flush := Z_FINISH })
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
    full_frame_weaken (state_store_full_frame h ds { d with last_flush := Z_FINISH })
      (fun _ same => Or.inr (Or.inl (Or.inl same)))
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_FINISH } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, account, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
      public_busy_slow_finish_full_storage_execution (boundary0.strategy ready) boundary0.end_frontier
        buffers0 status level strategy pointer memory wrap ready inputValid
    have entry := public_busy_finish_entry boundary.good status queued nonnull positive inputValid lower upper
    exact ⟨used, produced, rc, after, z', result, entry.trans run, goodA, account, inputA, outputA,
      shape0.trans shapeA, full_frame_trans_shape frame0 frameA shape0,
      full_shape_live_change (shape0.trans shapeA), allocA, nextA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨after, z', result, run, goodA, account, inputA, outputA⟩ :=
        public_pending_exhausted_counter_execution Z_FINISH boundary.good buffers pointer inputValid (by decide) (by decide)
          (fun _ => rfl) output enough boundary.bits pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, run, goodA, account, by simpa using inputA, outputA, ?_⟩
      exact public_pending_exhausted_run_full_storage boundary.good buffers pointer inputValid
        (by decide) (by decide) (fun _ => rfl) output enough boundary.bits pending run
    · have pending0 := last_flush_pending_bits boundary.good pending Z_FINISH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, pendingBase, flushRun, stateM, buffersM,
          accountM, _sizesM, storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have effectsM := flush_pending_low_run_counter_effects boundary0.good buffers0 pointer boundary.bits flushRun stateM.good.live.hz accountM
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, rc, after, z', result, tailRun, goodA, accountA, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
        public_busy_slow_finish_full_storage_execution (stateM.strategy (readyM left)) stateM.end_frontier
          buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output inputValid accountM)
      have entry := public_pending_finish_continue boundary.good stateM.good nonnull positive inputValid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have owned : DeflateOwned ds dm = DeflateOwned ds d := ConfigFrame.owned
        (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm)
      rw [owned] at frameA
      have shapeM := shape0.trans storageM.shape
      have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
      have shape := shapeM.trans shapeA
      have frame := full_frame_trans_shape frameM frameA shapeM
      refine ⟨used, produced + laterProduced, rc, after, z', result,
        entry.trans ((public_busy_header_skip stateM.good statusM).trans tailRun), goodA, ?_, ?_, ?_, shape, frame, full_shape_live_change shape,
          allocA.trans storageM.nalloc, nextA.trans storageM.nextBlk⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [inputA, effectsM.1]
      · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Complete accepted BUSY NO_FLUSH calls retain exact totals, including empty retries. -/
theorem public_busy_no_flush_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have shape0 := shape_setD boundary.good.live.hs { d with last_flush := Z_NO_FLUSH }
  have frame0 : Frame h (setD h ds { d with last_flush := Z_NO_FLUSH })
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
    full_frame_weaken (state_store_full_frame h ds { d with last_flush := Z_NO_FLUSH })
      (fun _ same => Or.inr (Or.inl (Or.inl same)))
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_NO_FLUSH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, after, z', result, run, goodA, accountA, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
      public_busy_slow_no_flush_full_storage_execution boundary0 buffers0 status level strategy pointer memory wrap ready valid
    have resumed : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2 := by
      rcases resume with impossible | input | retry | initial
      · exact False.elim (impossible queued)
      · exact Or.inl input
      · exact Or.inr (Or.inl retry)
      · exact Or.inr (Or.inr initial)
    have entry := public_busy_no_flush_resuming_entry boundary.good status queued nonnull positive valid lower upper resumed
    exact ⟨used, produced, after, z', result, entry.trans run, goodA, accountA, inputA, outputA,
      shape0.trans shapeA, full_frame_trans_shape frame0 frameA shape0,
      full_shape_live_change (shape0.trans shapeA), allocA, nextA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨after, z', result, run, goodA, accountA, inputA, outputA⟩ :=
        public_pending_exhausted_counter_execution Z_NO_FLUSH boundary.good buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough boundary.bits pending
      refine ⟨0, z.avail_out.toNat, after, z', result, run, goodA, accountA, by simpa using inputA, outputA, ?_⟩
      exact public_pending_exhausted_run_full_storage boundary.good buffers pointer valid
        (by decide) (by decide) (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible) output enough boundary.bits pending run
    · have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, pendingBase, flushRun, stateM, buffersM,
          accountM, _sizesM, storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have effectsM := flush_pending_low_run_counter_effects boundary0.good buffers0 pointer boundary.bits flushRun stateM.good.live.hz accountM
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, after, z', result, run, goodA, accountA, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
        public_busy_slow_no_flush_full_storage_execution stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output valid accountM)
      have entry := public_pending_no_flush_continue boundary.good stateM.good status nonnull positive valid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have owned : DeflateOwned ds dm = DeflateOwned ds d := ConfigFrame.owned
        (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm)
      rw [owned] at frameA
      have shapeM := shape0.trans storageM.shape
      have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
      have shape := shapeM.trans shapeA
      have frame := full_frame_trans_shape frameM frameA shapeM
      refine ⟨used, produced + laterProduced, after, z', result,
        entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans run), goodA, ?_, ?_, ?_, shape, frame, full_shape_live_change shape,
          allocA.trans storageM.nalloc, nextA.trans storageM.nextBlk⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [inputA, effectsM.1]
      · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]

end Zlib.Deflate.Engine.Proofs
