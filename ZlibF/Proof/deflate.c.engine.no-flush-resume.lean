import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»

/-! # Accepted NO_FLUSH requests include empty-input retry -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A BUSY NO_FLUSH entry with input or a negative retry marker reaches
actual data dispatch after recording NO_FLUSH. Its legal last-flush range
makes the actual rank evaluation total. -/
theorem public_busy_no_flush_resuming_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) (resume : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2) :
    deflate (some r) Z_NO_FLUSH h =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH
        (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
  have good0 := last_flush_good good Z_NO_FLUSH
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
      (setD h ds { d with last_flush := Z_NO_FLUSH }) =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
    unfold publicZlibHeader
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have noDuplicate : (z.avail_in == 0 && decide ((0 : Int32) ≤ rank) && (Z_NO_FLUSH != Z_FINISH)) = false := by
    rcases resume with nonempty | old | old
    · simp [nonempty]
    · have evaluated : RANK d.last_flush = pure (-2) := by rw [old]; rfl
      have value : rank = -2 := (Prod.mk.inj (Except.ok.inj (congrFun (ranked.symm.trans evaluated) h))).1
      rw [value]
      simp only [show decide ((0 : Int32) ≤ -2) = false from rfl, Bool.and_false, Bool.false_and]
    · have evaluated : RANK d.last_flush = pure (-4) := by rw [old]; rfl
      have value : rank = -4 := (Prod.mk.inj (Except.ok.inj (congrFun (ranked.symm.trans evaluated) h))).1
      rw [value]
      simp only [show decide ((0 : Int32) ≤ -4) = false from rfl, Bool.and_false, Bool.false_and]
  have checked := stateCheck_live good.live
  have rankFinish : RANK Z_NO_FLUSH = pure 0 := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide, show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending,
    noDuplicate, Bool.false_and, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankFinish, ranked, show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  simpa only [status, pending] using header



/-- A complete accepted BUSY NO_FLUSH call returns the same working boundary,
including empty-input retry requests, old pending output and every positive
raw capacity. Empty-input duplicate requests have their separate refusal. -/
theorem public_default_busy_no_flush_accepted {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
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
      public_busy_slow_no_flush_buffered boundary0 buffers0 status level strategy pointer memory wrap ready valid
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
          _outA, lastA, _count, _bits, fields, _bytes, _pendingA, _bitsA⟩ :=
        public_pending_buffered_exhausted Z_NO_FLUSH boundary buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough pending
      refine ⟨0, z.avail_out.toNat, after, z', result, input, origin, base, xs, run, stateA, buffersA, accountA, ?_, Or.inl lastA⟩
      rw [fields]; exact status
    · have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
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
      obtain ⟨used, laterProduced, after, z', result, nextInput, nextOrigin, nextBase, ys,
          run, stateA, buffersA, accountA, statusA, lastA⟩ :=
        public_busy_slow_no_flush_buffered stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
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
every positive raw output capacity are included. Duplicate requests and calls after FINISH_STATE are separate refusal cases. -/
theorem DefaultFinishBoundary.no_flush_resuming {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
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
      exact public_default_first_no_flush_buffered start level state buffers pointer output boundary.configuration.memory valid
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_default_busy_no_flush_accepted state buffers status level strategy pointer output
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

end Zlib.Deflate.Engine.Proofs
