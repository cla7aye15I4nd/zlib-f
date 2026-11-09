import ZlibF.Proof.«deflate.c.engine.generic-foreign-first-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-no-flush-data»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-busy-finish-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-finishing-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A complete accepted BUSY NO_FLUSH call returns the same working boundary,
including empty-input retry requests, old pending output and every positive
foreign depth capacity. Empty-input duplicate requests have their separate refusal. -/
theorem public_foreign_busy_no_flush_resuming_phase {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_NO_FLUSH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      default_foreign_public_busy_slow_no_flush_buffered boundary0 buffers0 status level strategy pointer memory wrap ready valid
    have resumed : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2 := by
      rcases resume with impossible | input | retry | initial
      · exact False.elim (impossible queued)
      · exact Or.inl input
      · exact Or.inr (Or.inl retry)
      · exact Or.inr (Or.inr initial)
    have entry := public_busy_no_flush_resuming_entry boundary.good status queued nonnull positive valid lower upper resumed
    exact ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, entry.trans run,
      stateA, buffersA, accountA, statusA, lastA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, accountA, _sizes, _storage,
          _outA, lastA, _count, _bits, fields, _bytes, _pendingA, _bitsA,_frameA⟩ :=
        public_pending_buffered_exhausted_foreign Z_NO_FLUSH boundary buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough pending
      refine ⟨0, z.avail_out.toNat, after, z', result, input, origin, base, xs, run, stateA, buffersA, accountA, ?_, Or.inl lastA⟩
      rw [fields]; exact status
    · have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM,_frameM⟩ :=
        flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
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
      obtain ⟨used, laterProduced, after, z', result, nextInput, nextOrigin, nextBase, ys,
          run, stateA, buffersA, accountA, statusA, lastA⟩ :=
        default_foreign_public_busy_slow_no_flush_buffered stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output valid accountM)
      have entry := public_pending_no_flush_continue boundary.good stateM.good status nonnull positive valid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have lastM : dm.last_flush = Z_NO_FLUSH := by rw [fields]
      rw [lastM] at lastA
      refine ⟨used, produced + laterProduced, after, z', result, nextInput, nextOrigin, nextBase, ys,
        entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans run), stateA, buffersA, ?_, statusA, lastA⟩
      simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
/-- Every accepted NO_FLUSH request, including empty-input retry, preserves the same
initialized protocol used by every later FINISH call. Pending output and
every positive foreign depth output capacity are included. Duplicate requests and calls after FINISH_STATE are separate refusal cases. -/
theorem DefaultFinishBoundary.foreign_no_flush_resuming {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (resume : d.status = BUSY_STATE → d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (unfinished : d.status ≠ FINISH_STATE) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE := by
  have executed : ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      exact default_foreign_first_no_flush_buffered start level state buffers pointer output boundary.configuration.memory valid
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_foreign_busy_no_flush_resuming_phase state buffers status level strategy pointer output
        boundary.configuration.memory boundary.configuration.wrap valid (resume status) boundary.lower boundary.upper
    · exact False.elim (unfinished finishing.status)
  obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys,
    run, stateA, buffersA, accountA, statusA, lastA⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_NO_FLUSH) (value := Z_OK) boundary.reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases lastA with eq | eq <;> rw [eq] <;> decide
  exact ⟨used, produced, after, z', result, run,
    ⟨stateA.good, reachableA, boundary.configuration,
      Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA⟩), bounds.1, bounds.2⟩,
    buffersA, accountA, statusA⟩

/-- The accepted real FINISH call preserves the initialized protocol and
extends the actual public reachable history. No loop bound, byte budget
or output-capacity lower bound beyond a positive public buffer is assumed.
New input after FINISH_STATE is the separate refusal case. -/
theorem DefaultFinishBoundary.foreign_finish {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have executed : ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ PublicFinishPhase after r ds z' result config ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, _bits, phaseA, last, ended⟩ :=
        default_foreign_public_first_finish_phase start level state buffers pointer output boundary.configuration.memory valid
      exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, _bits, phaseA, last, ended⟩ :=
        default_foreign_public_busy_finish_phase state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩
    · obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, emptyA, ended⟩ :=
        public_default_foreign_finishing_phase boundary.good buffers finishing pointer (accepted finishing.status) output boundary.lower boundary.upper
      exact ⟨0, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, Or.inr phaseA, last,
        fun done => ⟨phaseA.status, (ended done).1, emptyA, phaseA.lookahead, (ended done).2, phaseA.bits⟩⟩
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) boundary.reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases last with eq | eq <;> rw [eq] <;> decide
  exact ⟨used, produced, rc, after, z', result, run,
    ⟨goodA, reachableA, boundary.configuration, Or.inr phaseA, bounds.1, bounds.2⟩, buffersA, account, allowed, ended⟩


end Zlib.Deflate.Engine.Proofs
