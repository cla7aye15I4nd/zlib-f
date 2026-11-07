import ZlibF.Proof.«deflate.c.engine.finish-ready-call»
import ZlibF.Proof.«deflate.c.engine.finish-status»
import ZlibF.Proof.«deflate.c.engine.ordinary-call-counters»
import ZlibF.Proof.«deflate.c.engine.trailer-counters»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»

/-! # Both actual default public data paths have exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real default BUSY FINISH dispatch, controls and trailer compose exact totals. -/
theorem public_busy_slow_finish_counter_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, _endM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishedM, classification⟩ :=
    deflate_slow_finish_ready boundary frontier buffers positive pointer memory wrap publish inputValid
  have effectsM := deflate_slow_finish_run_counter_effects boundary frontier buffers positive pointer memory wrap
    publish inputValid strategyRun stateM.good.live.hz accountM
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    exact ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good stateM.good (-1), accountM, effectsM⟩
  · subst ret
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    exact ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good goodS (-1), accountM, effectsM⟩
  · subst ret
    have finished := finishedM (by decide)
    have ready := stateM.resume remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := by
      have eq := congrArg EngineConfig.wrap stateM.configuration
      exact eq.trans wrap
    obtain ⟨trailerProduced, after, z', result, trailerRun, goodA, accountA, inputA, outputA⟩ :=
      zlib_trailer_counter_execution goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, ?_, inputA.trans effectsM.1, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Actual BUSY NO_FLUSH dispatch includes idle calls and exhausted prepared output. -/
theorem public_busy_slow_no_flush_counter_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have effectsM := deflate_slow_no_flush_run_counter_effects (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      exact ⟨used, produced, _, zm, _, source.trans returned, stateF.good, accountM, effectsM⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, middle, zm, dm, source.trans returned, stateM.good, accountM, effectsM⟩
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, public_default_empty_data boundary.good status empty look,
      boundary.good, stream_accounting_zero z, by simp, by simp⟩

end Zlib.Deflate.Engine.Proofs
