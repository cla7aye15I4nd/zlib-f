import ZlibF.Proof.«deflate.c.engine.block-protocol»
import ZlibF.Proof.«deflate.c.engine.public-pending-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»

/-! # Exact effects of every accepted BUSY default BLOCK call -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual BUSY BLOCK entry, old pending publication, duplicate refusal
and complete data execution share exact wrapping totals, caller output
interval, object frame and allocation ledger. Public output is positive
and raw; the earlier entry guards and first header are separate cases. -/
theorem public_busy_block_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_BLOCK h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have state0 := last_flush_buffered_boundary boundary Z_BLOCK
  have buffers0 := last_flush_buffers boundary.good buffers Z_BLOCK
  have shape0 := shape_setD boundary.good.live.hs { d with last_flush := Z_BLOCK }
  have frame0 : Frame h (setD h ds { d with last_flush := Z_BLOCK })
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
  have interval0 : RawOutputInterval h (setD h ds { d with last_flush := Z_BLOCK }) ob oo 0 := .of_same rfl
  by_cases queued : d.pending = 0
  · obtain ⟨current, old, _rank, _oldRank, source⟩ := public_busy_valid_entry_choice boundary.good
      status queued nonnull positive inputValid lower upper Z_BLOCK (by decide) (by decide)
    by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && Z_BLOCK != Z_FINISH) = true
    · rw [if_pos duplicate] at source
      obtain ⟨message, refused⟩ := err_return_run state0.good.live.hz Z_BUF_ERROR
      let z' := { z with msg := message }
      have goodA := stream_control_good (z' := z') state0.good rfl boundary.good.live.zalloc boundary.good.live.zfree
      have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
      obtain ⟨shapeE, frameE, _liveE, allocE, nextE⟩ := err_return_run_full_storage state0.good.live.hz refused
      have private0 : Frame h (setD h ds { d with last_flush := Z_BLOCK })
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
        full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
      have privateE : Frame (setD h ds { d with last_flush := Z_BLOCK })
          (r.put (setD h ds { d with last_flush := Z_BLOCK }) z')
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
        full_frame_weaken frameE (fun _ root => Or.inl root)
      have privateFrame := full_frame_trans_shape private0 privateE shape0
      have interval := RawOutputInterval.of_private_frame (produced := 0) boundary.good buffers pointer privateFrame
      have shape := shape0.trans shapeE
      exact ⟨0, 0, Z_BUF_ERROR, _, z', _, source.trans refused, goodA, account,
        by simp [z'], by simp [z'], interval, shape, full_private_frame_add_output privateFrame,
        full_shape_live_change shape, allocE, nextE⟩
    · rw [if_neg duplicate] at source
      have ready : PublishReady { d with last_flush := Z_BLOCK } :=
        ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
      obtain ⟨used, produced, after, z', result, run, goodA, _buffersA, accountA,
          inputA, outputA, intervalA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
        public_busy_slow_block_effect_execution (state0.strategy ready) state0.end_frontier buffers0
          status level strategy pointer memory wrap ready inputValid
      have interval : RawOutputInterval h after ob oo produced := by
        simpa only [Nat.zero_add] using interval0.trans intervalA
      have shape := shape0.trans shapeA
      exact ⟨used, produced, Z_OK, after, z', result, source.trans run, goodA, accountA,
        inputA, outputA, interval, shape, full_frame_trans_shape frame0 frameA shape0,
        full_shape_live_change shape, allocA, nextA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    have finishAllowed : d.status = FINISH_STATE → Z_BLOCK = Z_FINISH := by
      intro impossible
      rw [status] at impossible
      cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨after, z', result, run, goodA, accountA, inputA, outputA, interval⟩ :=
        public_pending_exhausted_output_execution Z_BLOCK boundary.good buffers pointer inputValid
          (by decide) (by decide) finishAllowed output enough boundary.bits pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, run, goodA, accountA,
        by simpa using inputA, outputA, interval, ?_⟩
      exact public_pending_exhausted_run_full_storage boundary.good buffers pointer inputValid
        (by decide) (by decide) finishAllowed output enough boundary.bits pending run
    · have pending0 := last_flush_pending_bits boundary.good pending Z_BLOCK
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, pendingBase, flushRun, stateM, buffersM,
          accountM, _sizesM, storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary state0 buffers0 pointer pending0
      have totalsM := flush_pending_low_run_counter_effects state0.good buffers0 pointer boundary.bits
        flushRun stateM.good.live.hz accountM
      have intervalM := flush_pending_low_run_output_effect state0.good buffers0 pointer boundary.bits
        flushRun stateM.good.live.hz accountM
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
      obtain ⟨used, laterProduced, after, z', result, tailRun, goodA, _buffersA, accountA,
          inputA, outputA, intervalA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
        public_busy_slow_block_effect_execution (stateM.strategy (readyM left)) stateM.end_frontier buffersM
          statusM levelM strategyM pointerM memory wrap (readyM left) (input_valid_accounting_output inputValid accountM)
      have entry := public_pending_valid_continue boundary.good stateM.good status nonnull positive inputValid queued
        Z_BLOCK (by decide) (by decide) flushRun
        (by intro zero; rw [zero] at left; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have owned : DeflateOwned ds dm = DeflateOwned ds d := ConfigFrame.owned
        (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm)
      rw [owned] at frameA
      have shapeM := shape0.trans storageM.shape
      have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
      have intervalPrefix : RawOutputInterval h middle ob oo produced := by
        simpa only [Nat.zero_add] using interval0.trans intervalM
      have interval := intervalPrefix.trans intervalA
      have shape := shapeM.trans shapeA
      refine ⟨used, produced + laterProduced, Z_OK, after, z', result,
        entry.trans ((public_busy_header_skip_next stateM.good statusM _).trans tailRun), goodA,
        ?_, ?_, ?_, interval, shape, full_frame_trans_shape frameM frameA shapeM, full_shape_live_change shape,
        allocA.trans storageM.nalloc, nextA.trans storageM.nextBlk⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [inputA, totalsM.1]
      · rw [outputA, totalsM.2, UInt64.ofNat_add, UInt64.add_assoc]

end Zlib.Deflate.Engine.Proofs
