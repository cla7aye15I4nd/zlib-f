import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-call»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-return-safety»
import ZlibF.Proof.«deflate.c.engine.public-slow-block»

/-! # Actual default BLOCK dispatch and public return preserve the engine -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The BUSY default BLOCK data path executes the complete real strategy
and actual public return. Both frontiers, caller buffers and accounting
survive every output capacity. The full entry and initialized public
history theorem remain separate obligations. -/
theorem public_foreign_busy_slow_block_phase {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result base' ys extended nextOrigin,
      publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      (result.pending=0 → result.pending_out=result.pending_buf) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, endM, buffersM, accountM, agreesM, endpointM, baseM, classification,controls,doneReady⟩ :=
    default_foreign_deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_BLOCK (by decide) (by decide)
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_BLOCK (by decide)]
    simp only [bind_app, strategyRun]
  have statusM : middleD.status = BUSY_STATE := controls.status.trans status
  have stopped : publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle =
      .ok (Z_OK, setD middle ds { middleD with last_flush := -1 }) →
      ∃ used produced after z' result base' ys extended nextOrigin,
        publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
        StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
        StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
        (∀ i, i < origin + fillEnd d → extended i = input i) ∧
        nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
        result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      (result.pending=0 → result.pending_out=result.pending_buf) := by
    intro run
    exact ⟨used, produced, _, middleZ, _, middleBase, ys, extended, nextOrigin, sourceRun.trans run,
      last_flush_strategy_boundary stateM (-1), last_flush_end_frontier endM (-1),
      last_flush_buffers stateM.good buffersM (-1), accountM, agreesM, endpointM, baseM, statusM, Or.inr rfl,controls.empty_cursor⟩
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _input, _look, _symbols⟩
  · subst ret
    exact stopped (public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_BLOCK)
  · subst ret
    have readyM := (doneReady rfl).1
    have run := public_strategy_block_done_ready stateM.good readyM
    by_cases exhausted : (middleZ.avail_out == 0) = true
    · exact stopped (by simpa only [exhausted, ite_true] using run)
    · refine ⟨used, produced, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
        sourceRun.trans ?_, stateM, endM, buffersM, accountM, agreesM, endpointM, baseM, statusM, Or.inl controls.last_flush,controls.empty_cursor⟩
      simpa only [exhausted, Bool.false_eq_true, ite_false] using run

end Zlib.Deflate.Engine.Proofs
