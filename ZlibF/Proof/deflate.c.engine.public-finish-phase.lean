import ZlibF.Proof.«deflate.c.engine.finish-buffered»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»
import ZlibF.Proof.«deflate.c.engine.finish-status»

/-! # Public FINISH working and finishing phases on actual return heaps -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- After the final block, only pending publication and the one-time trailer remain. -/
structure FinishingPhase (d : DeflateState) (config : EngineConfig) : Prop where
  status : d.status = FINISH_STATE
  lookahead : d.lookahead = 0
  bits : d.bi_valid.toInt = 0
  configuration : engineConfig d = { config with wrap := d.wrap }
  wrapper : d.wrap = 1 ∨ d.wrap = -1
  cursor : d.wrap = 1 → d.pending = 0 → d.pending_out = d.pending_buf

/-- Internal FINISH protocol phases. Full public histories and output refinement remain separate. -/
def PublicFinishPhase (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) (config : EngineConfig) : Prop :=
  (∃ input origin base xs, BufferedBoundary h r ds z d input origin base xs config ∧ d.status = BUSY_STATE) ∨
    FinishingPhase d config

theorem buffered_finish_status {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) :
    BufferedBoundary (setD h ds { d with status := FINISH_STATE }) r ds z
      { d with status := FINISH_STATE } input origin base xs config :=
  buffered_control_transfer boundary (finish_status_good boundary.good)
    (fun _ _ => rfl) rfl rfl rfl boundary.empty_cursor

theorem finishing_phase_of_buffered {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (status : d.status = FINISH_STATE) (look : d.lookahead = 0) (bits : d.bi_valid.toInt = 0) (wrap : d.wrap = 1) :
    FinishingPhase d config := by
  refine ⟨status, look, bits, ?_, Or.inl wrap, fun _ => boundary.empty_cursor⟩
  have value : d.wrap = config.wrap := congrArg EngineConfig.wrap boundary.configuration
  rw [boundary.configuration, value]

/-- Accepted default data dispatch preserves a working or finishing phase.
The full entry and output/frame refinement are separate obligations. -/
theorem public_busy_slow_finish_phase {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishing, classification⟩ :=
    deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
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
      Or.inl ⟨extended, nextOrigin, middleBase, ys, stateF, controlsM.status.trans status⟩, Or.inl rfl, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
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
      last_flush_buffers goodS buffersS (-1), accountM, Or.inl rfl, stateF.bits, Or.inr phase, Or.inl rfl, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
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
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, Or.inr phase, ?_, ?_⟩
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

end Zlib.Deflate.Engine.Proofs
