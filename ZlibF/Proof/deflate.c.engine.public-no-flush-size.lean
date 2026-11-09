import ZlibF.Proof.«deflate.c.engine.no-flush-counted-size»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-pending-size»

/-! # Actual BUSY NO_FLUSH dispatch retains the counted prefix budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Prepared BUSY NO_FLUSH dispatch spends only the actual full-block
budget. Idle dispatch and the output-full last-flush update are included.
No final-block charge is spent by repeated input/output offers. Public
entry/header and complete utility histories compose separately. -/
theorem public_busy_no_flush_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = Z_DEFAULT_STRATEGY)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (window : config.windowBits = 15) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ used produced blocks after z' result extended nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - base) + 5 * blocks := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]; decide
    have cfgStrategy : config.strategy = Z_DEFAULT_STRATEGY :=
      (congrArg EngineConfig.strategy boundary.configuration).symm.trans strategy
    obtain ⟨used, produced, blocks, middle, zm, dm, nextInput, nextOrigin, nextBase, ys,
      run, stateM, endM, buffersM, accountM, endpointM, baseM, candidateM, floorM, qualityM, minimumM, costM⟩ :=
      deflate_slow_no_flush_counted_size (boundary.strategy publish) boundary.end_frontier buffers positive pointer
        memory wrap window cfgStrategy publish inputValid candidate floor quality
    obtain ⟨_usedOld, _producedOld, other, _otherZ, otherD, _baseOld, _symbolsOld, _inputOld, _originOld,
      oldRun, oldState, controls, _oldBuffers, _oldRest⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have heaps : other = middle := (Prod.mk.inj (Except.ok.inj (oldRun.symm.trans run))).2
    rw [heaps] at oldState
    have states : otherD = dm := Option.some.inj (oldState.good.live.hs.symm.trans stateM.good.live.hs)
    rw [states] at controls
    have bufferedM := stateM.buffered endM controls.empty_cursor
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, run]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary bufferedM (-1)
      exact ⟨used, produced, blocks, _, zm, _, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateF, last_flush_buffers stateM.good buffersM (-1), accountM, endpointM, baseM,
        candidateM, floorM, qualityM, minimumM, costM⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, blocks, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        bufferedM, buffersM, accountM, endpointM, baseM, candidateM, floorM, qualityM, minimumM, costM⟩
  · have empty : z.avail_in = 0 := by by_cases zero : z.avail_in = 0; exact zero; exact (active (Or.inl zero)).elim
    have look : d.lookahead = 0 := by by_cases zero : d.lookahead = 0; exact zero; exact (active (Or.inr zero)).elim
    refine ⟨0, 0, 0, h, z, d, input, origin, base, xs, public_default_empty_data boundary.good status empty look,
      boundary, buffers, stream_accounting_zero z, by simp, Nat.le_refl _, candidate, floor, quality, by simp, ?_⟩
    rw [publish.1, UInt64.toNat_zero]; simp

/-- A complete positive-output BUSY NO_FLUSH call retains the counted
prefix budget from arbitrary pending output. Pending-only early OK and
a complete drain followed by strategy work both preserve the potential.
The last-flush bounds and new input come from the utility protocol. -/
theorem public_default_busy_no_flush_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = Z_DEFAULT_STRATEGY)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) (nonempty : z.avail_in ≠ 0)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ used produced blocks after z' result extended nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - base) + 5 * blocks := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_NO_FLUSH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
      run, stateA, buffersA, accountA, endpointA, baseA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
      public_busy_no_flush_counted_size boundary0 buffers0 status level strategy pointer memory wrap window ready valid
        candidate floor quality
    have entry := public_busy_no_flush_entry boundary.good status queued nonnull positive valid lower upper nonempty
    refine ⟨used, produced, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys, entry.trans run,
      stateA, buffersA, accountA, endpointA, baseA, candidateA, floorA, qualityA, minimumA, ?_⟩
    simpa only [queued, UInt64.toNat_zero, Nat.zero_add] using costA
  · by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨after, z', result, run, stateA, buffersA, accountA, _zeroA, endpointA, exactCost, candidateA, floorA⟩ :=
        public_pending_exhausted_byte_potential Z_NO_FLUSH boundary buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough
      refine ⟨0, z.avail_out.toNat, 0, after, z', result, input, origin, base, xs, run, stateA, buffersA, accountA,
        by rw [endpointA]; simp, Nat.le_refl _, candidateA candidate, floorA floor, quality, by simp, ?_⟩
      simpa only [Nat.sub_self, Nat.add_zero, Nat.mul_zero] using Nat.le_of_eq exactCost
    · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
      have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, drained, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
        accountM, _sizesM, _storageM, amount, pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = Z_DEFAULT_STRATEGY := by rw [fields]; exact strategy
      have drainedEq : drained = d.pending.toNat := by
        change drained = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        exact amount
      have left : 0 < zm.avail_out.toNat := by have balance := accountM.2.2.2.1; omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + drained) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      have candidateM : ShortCandidateQuality dm := by rw [fields]; exact candidate
      have floorM : StoredSourceFloor dm := by rw [fields]; exact floor
      obtain ⟨used, amountA, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
        run, stateA, buffersA, accountA, endpointA, baseA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
        public_busy_no_flush_counted_size stateM buffersM statusM levelM strategyM pointerM memory wrap window
          (readyM left) (input_valid_accounting_output valid accountM) candidateM floorM quality
      have entry := public_pending_no_flush_continue boundary.good stateM.good status nonnull positive valid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have endpointM : fillEnd dm = fillEnd d := by rw [fields]; rfl
      have bitsM : dm.bi_valid = d.bi_valid := by rw [fields]
      rw [endpointM] at endpointA
      rw [bitsM] at costA
      refine ⟨used, drained + amountA, blocks, after, z', result, nextInput, nextOrigin, nextBase, ys,
        entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans run), stateA, buffersA,
        ?_, endpointA, baseA, candidateA, floorA, qualityA, minimumA, ?_⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · omega

end Zlib.Deflate.Engine.Proofs
