import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-data-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-busy-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-counter»
import ZlibF.Proof.«deflate.c.engine.public-busy-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete BUSY non-FINISH calls compose old pending output, real strategy and trailer totals. -/
theorem public_foreign_busy_nonfinish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (flush : Int32) (flag : flush=Z_NO_FLUSH ∨ flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers boundary.good buffers flush
  have shape0 := shape_setD boundary.good.live.hs { d with last_flush := flush }
  have private0 : Frame h (setD h ds {d with last_flush:=flush}) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
  have frame0 := full_private_frame_add_output (ob:=owner) private0
  have view0 := private_frame_foreign_output_same boundary.good buffers pointer private0
  obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := flush } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨current,old,_currentRank,_oldRank,source⟩ := public_busy_valid_entry_choice boundary.good status queued nonnull positive inputValid lower upper flush flagLo flagHi
    by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && flush != Z_FINISH) = true
    · rw [ite_eq_left duplicate] at source
      obtain ⟨message,refused⟩ := err_return_run boundary0.good.live.hz Z_BUF_ERROR
      let z' := {z with msg:=message}
      have goodA := stream_control_good (z':=z') boundary0.good rfl boundary.good.live.zalloc boundary.good.live.zfree
      have shapeA := shape_put boundary0.good.live.hz z'
      have frameA := stream_store_full_frame (setD h ds {d with last_flush:=flush}) r z'
      have shape := shape0.trans shapeA
      have privateFrame := full_frame_trans_shape private0 (full_frame_weaken frameA (fun _ yes => Or.inl yes)) shape0
      have precise := finishing_foreign_private_zero_frame boundary.good buffers pointer shape privateFrame
      exact ⟨0,0,Z_BUF_ERROR,_,z',_,source.trans refused,goodA,stream_accounting_zero z,
        by simp [z'],by simp [z'],shape,full_private_frame_add_output privateFrame,full_shape_live_change shape,by simp,by simp,precise⟩
    · rw [ite_eq_right duplicate] at source
      obtain ⟨used, produced, after, z', result, _nextInput,_nextOrigin,_nextBase,_ys,run,stateA,_buffersA,account,_statusA,_lastA,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
        public_foreign_busy_nonfinish_data_full_storage_execution boundary0 buffers0 status level strategy pointer memory wrap ready inputValid flush flag
      have goodA := stateA.good
      have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        rw [pointer] at preciseA ⊢
        exact generic_wrapper_foreign_private_prefix private0 view0 preciseA
      exact ⟨used, produced, Z_OK, after, z', result, source.trans run, goodA, account, inputA, outputA,
        shape0.trans shapeA, full_frame_trans_shape frame0 frameA shape0,
        full_shape_live_change (shape0.trans shapeA), allocA, nextA,precise⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨pb,after,z',result,_written,_remaining,pendingBase,run,stateA,_buffersA,accountA,_sizes,storage,
          _output,_last,_count,_bits,_fields,_bytes,_pendingA,_wire,preciseSmall⟩ :=
        public_pending_buffered_exhausted_foreign flush boundary buffers pointer inputValid
          flagLo flagHi (by intro impossible;rw [status] at impossible;cases (show BUSY_STATE≠FINISH_STATE from by decide) impossible) output enough pending
      obtain ⟨other,otherZ,_otherD,tested,goodOther,_otherAccount,inputOther,outputOther⟩ :=
        public_pending_exhausted_foreign_counter_execution flush boundary.good buffers pointer inputValid
          flagLo flagHi (by intro impossible;rw [status] at impossible;cases (show BUSY_STATE≠FINISH_STATE from by decide) impossible) output enough boundary.bits pending
      have same := actual_run_stream_unique tested run goodOther.live.hz stateA.good.live.hz
      rw [same] at inputOther outputOther
      have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,z.avail_out.toNat⟩] :=
        ⟨full_frame_weaken preciseSmall.1 (fun _ yes => yes.elim Or.inl (fun isState => Or.inr (Or.inl isState))),preciseSmall.2⟩
      exact ⟨0,z.avail_out.toNat,Z_OK,after,z',result,run,stateA.good,accountA,by simpa using inputOther,outputOther,
        storage.shape,storage.private_frame pendingBase,full_shape_live_change storage.shape,storage.nalloc,storage.nextBlk,precise⟩
    · have pending0 := last_flush_pending_bits boundary.good pending flush
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, pendingBase, flushRun, stateM, buffersM,
          accountM, _sizesM, storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM,preciseM⟩ :=
        flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
      have scalarM := flush_pending_low_foreign_run_scalar_effects boundary0.good buffers0 pointer boundary.bits flushRun stateM.good.live.hz accountM
      have effectsM := And.intro scalarM.2.1 scalarM.2.2.1
      have preciseM' : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        have wide : BufferFrame (setD h ds {d with last_flush:=flush}) middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] :=
          ⟨full_frame_weaken preciseM.1 (fun _ yes => yes.elim Or.inl (fun isState => Or.inr (Or.inl isState))),preciseM.2⟩
        rw [pointer] at wide ⊢
        exact generic_wrapper_foreign_private_prefix private0 view0 wide
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, after, z', result, _inputA,_originA,_baseA,_ysA,tailRun,stateA,_buffersA,accountA,_statusA,_lastA,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
        public_foreign_busy_nonfinish_data_full_storage_execution stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output inputValid accountM) flush flag
      have goodA := stateA.good
      have entry := public_pending_valid_continue boundary.good stateM.good status nonnull positive inputValid queued flush flagLo flagHi flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have owned : DeflateOwned ds dm = DeflateOwned ds d := ConfigFrame.owned
        (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm)
      rw [owned] at frameA preciseA
      have shapeM := shape0.trans storageM.shape
      have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
      have shape := shapeM.trans shapeA
      have frame := full_frame_trans_shape frameM frameA shapeM
      have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced+laterProduced⟩] := by
        rw [pointer] at preciseM' ⊢
        rw [pointerM] at preciseA
        exact foreign_buffer_frame_adjacent preciseM' preciseA shapeM shapeA boundary.good.uniq get
          (caller_foreign_owner_outside boundary.good buffers pointer)
      refine ⟨used, produced + laterProduced, Z_OK, after, z', result,
        entry.trans ((public_busy_header_skip_next stateM.good statusM _).trans tailRun), goodA, ?_, ?_, ?_, shape, frame, full_shape_live_change shape,
          allocA.trans storageM.nalloc, nextA.trans storageM.nextBlk,precise⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [inputA, effectsM.1]
      · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]


end Zlib.Deflate.Engine.Proofs
