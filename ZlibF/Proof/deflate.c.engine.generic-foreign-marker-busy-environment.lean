import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-data-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-busy-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-buffered»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual positive-output BUSY marker call preserves the selected build's
static tables. Pending output, empty retries and duplicate-request refusals are included. -/
theorem public_foreign_busy_marker_run_static {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (output : 0<z.avail_out.toNat)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1)
    (valid : z.avail_in≠0 → z.next_in≠.null)
    (lower : -2≤d.last_flush.toInt) (upper : d.last_flush.toInt≤5)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK)
    (run : deflate (some r) flush h=.ok (rc,after)) : after.static=h.static := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl|rfl|rfl|rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl|rfl|rfl|rfl <;> decide
  have nonnull : z.next_out≠.null := by rw [pointer];intro impossible;cases impossible
  have positive : z.avail_out≠0 := by intro zero;rw [zero] at output;contradiction
  have boundary0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers boundary.good buffers flush
  by_cases queued : d.pending=0
  · have ready : PublishReady {d with last_flush:=flush} := ⟨queued,boundary.empty_cursor queued,boundary.bits⟩
    obtain ⟨current,old,_currentRank,_oldRank,source⟩ := public_busy_valid_entry_choice boundary.good status queued nonnull positive valid lower upper flush flagLo flagHi
    by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && flush != Z_FINISH) = true
    · rw [ite_eq_left duplicate] at source
      exact (err_return_run_full_storage boundary0.good.live.hz (source.symm.trans run)).2.1.1.symm
    · rw [ite_eq_right duplicate] at source
      have kept := public_foreign_busy_marker_data_run_static boundary0 buffers0 status level strategy pointer memory wrap ready valid flush flag (source.symm.trans run)
      exact kept
  · obtain ⟨before,pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat≤d.pending.toNat
    · obtain ⟨_pb,other,_z',_result,_written,_remaining,_base,tested,_stateA,_buffersA,_accountA,_sizes,storage,_rest⟩ :=
        public_pending_buffered_exhausted_foreign flush boundary buffers pointer valid flagLo flagHi
          (by intro impossible;rw [status] at impossible;cases (show BUSY_STATE≠FINISH_STATE from by decide) impossible)
          output enough pending
      have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      exact heaps ▸ storage.frame.1.symm
    · have pending0 := last_flush_pending_bits boundary.good pending flush
      obtain ⟨_pb,produced,middle,zm,dm,_written,_remaining,_base,flushRun,stateM,buffersM,
          accountM,_sizesM,storageM,amount,_count,fields,readyM,_bytesM,_pendingM,_bitsM,_precise⟩ :=
        flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status=BUSY_STATE := by rw [fields];exact status
      have levelM : dm.level=6 := by rw [fields];exact level
      have strategyM : dm.strategy=0 := by rw [fields];exact strategy
      have left : 0<zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced=min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+produced) := by
        rw [accountM.2.2.2.2.2.1,pointer];rfl
      have entry := public_pending_valid_continue boundary.good stateM.good status nonnull positive valid queued flush flagLo flagHi flushRun
        (by intro zero;rw [zero] at left;contradiction)
        (by intro impossible;rw [statusM] at impossible;cases (show BUSY_STATE≠FINISH_STATE from by decide) impossible)
      have source := entry.trans (public_busy_header_skip_next stateM.good statusM _)
      have dataRun := source.symm.trans run
      have staticA := public_foreign_busy_marker_data_run_static stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
        (input_valid_accounting_output valid accountM) flush flag dataRun
      exact staticA.trans storageM.frame.1.symm

end Zlib.Deflate.Engine.Proofs
