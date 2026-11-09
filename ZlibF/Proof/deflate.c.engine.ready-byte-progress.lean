import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»
import ZlibF.Proof.«deflate.c.engine.public-data-finish-progress»
import ZlibF.Proof.«deflate.c.engine.finishing-progress»

/-! # Byte progress from actual slow-strategy exits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (prepared NO_FLUSH data tail).
The actual strategy stops with exhausted input or output. Nonempty input
and positive output therefore imply a consumed or emitted byte. -/
theorem public_busy_slow_no_flush_byte_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (output : 0 < z.avail_out.toNat) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (z.avail_in ≠ 0 → used ≠ 0 ∨ produced ≠ 0) := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      refine ⟨used, produced, _, zm, _, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateF, last_flush_buffers stateM.good buffersM (-1), accountM, controlsM.status.trans status, Or.inl rfl, ?_⟩
      · intro nonempty
        right
        have count := accountM.2.2.2.1
        rw [empty] at count
        simp only [UInt32.toNat_zero, Nat.zero_add] at count
        omega
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      refine ⟨used, produced, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateM, buffersM, accountM, controlsM.status.trans status, Or.inr controlsM.last_flush, ?_⟩
      · intro nonempty
        rcases _stopped with ⟨emptyIn, _⟩ | emptyOut
        · left
          have count := accountM.2.2.1
          have nonzero : z.avail_in.toNat ≠ 0 := fun zero => nonempty (UInt32.toNat_inj.mp zero)
          rw [emptyIn] at count
          simp only [UInt32.toNat_zero, Nat.zero_add] at count
          omega
        · right
          have count := accountM.2.2.2.1
          rw [emptyOut] at count
          simp only [UInt32.toNat_zero, Nat.zero_add] at count
          omega
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, input, origin, base, xs, public_default_empty_data boundary.good status empty look,
      boundary, buffers, stream_accounting_zero z, status, Or.inr rfl, fun nonempty => False.elim (nonempty empty)⟩


/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (prepared FINISH data tail).
An unfinished strategy exhausts output; the completed strategy publishes
the actual trailer. Either OK path emits a byte at positive capacity. -/
theorem public_busy_slow_finish_byte_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) ∧
      (rc = Z_OK → 0 < produced) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishing, classification, strictM⟩ :=
    deflate_slow_finish_buffered_progress boundary buffers positive pointer memory wrap publish output inputValid
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    have stateF := last_flush_buffered_boundary stateM (-1)
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers stateM.good buffersM (-1), accountM, Or.inl rfl, stateF.bits,
      Or.inl ⟨extended, nextOrigin, middleBase, ys, stateF, controlsM.status.trans status⟩, Or.inl rfl, ?_, (fun _ => by
        have balance := accountM.2.2.2.1
        rw [exhausted] at balance
        simp only [UInt32.toNat_zero, Nat.zero_add] at balance
        omega), ?_⟩
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · intro impossible
      have wrong : BUSY_STATE = FINISH_STATE := (controlsM.status.trans status).symm.trans impossible
      cases (by decide : BUSY_STATE ≠ FINISH_STATE) wrong
  · subst ret
    have finished := finishing (by decide)
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have stateS := buffered_finish_status stateM
    have stateF := last_flush_buffered_boundary stateS (-1)
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    have phase := finishing_phase_of_buffered stateF rfl finished.1 finished.2 wrapM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers goodS buffersS (-1), accountM, Or.inl rfl, stateF.bits, Or.inr phase, Or.inl rfl, ?_, ?_, fun _ => _empty⟩
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · intro _
      have balance := accountM.2.2.2.1
      rw [exhausted] at balance
      simp only [UInt32.toNat_zero, Nat.zero_add] at balance
      omega
  · subst ret
    have finished := finishing (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    obtain ⟨trailerProduced, after, z', result, _written, _pendingBits, trailerRun, goodA, buffersA, accountA,
      _sizes, _storage, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _trailerBits⟩ :=
      zlib_trailer_publish goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have phase : FinishingPhase result config := by
      refine ⟨by rw [fields], by rw [fields]; exact finished.1, bitsA, ?_, Or.inr wrapA, ?_⟩
      · rw [wrapA, fields]
        change { engineConfig middleD with wrap := -1 } = { config with wrap := -1 }
        rw [stateM.configuration]
      · intro positiveWrap
        rw [wrapA] at positiveWrap
        cases (show (-1 : Int32) ≠ 1 from by decide) positiveWrap
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, Or.inr phase, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · by_cases queued : result.pending = 0 <;> simp [queued]
    · rw [bitsA]
      decide
    · right
      rw [fields]
      exact controlsM.last_flush
    · intro ended
      have drained : result.pending = 0 := by
        by_cases queued : result.pending = 0
        · exact queued
        · simp [queued, show Z_OK ≠ Z_STREAM_END from by decide] at ended
      have inputA : z'.avail_in = 0 := by
        have count := accountA.2.2.1
        rw [empty] at count
        apply UInt32.toNat_inj.mp
        change z'.avail_in.toNat = 0
        change z'.avail_in.toNat + 0 = 0 at count
        omega
      exact ⟨phase.status, wrapA, inputA, phase.lookahead, drained, bitsA⟩

    · intro _
      have moved : 0 < trailerProduced := by
        rw [_amount]
        exact Nat.lt_min.mpr ⟨by decide, remaining⟩
      omega
    · intro _
      apply UInt32.toNat_inj.mp
      have count := accountA.2.2.1
      rw [empty] at count
      change z'.avail_in.toNat + 0 = 0 at count
      exact count

end Zlib.Deflate.Engine.Proofs
