import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»
import ZlibF.Proof.«deflate.c.engine.common-slow-source»

/-! # Exact output interval for slow levels four through nine -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual slow FINISH dispatch preserves the exact caller output interval
and total counters for every admitted slow level. -/
theorem public_common_slow_finish_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq]
    omega
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, _endM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishedM, classification⟩ :=
    deflate_slow_finish_ready boundary frontier buffers positive pointer memory wrap publish inputValid
  have effectsM := deflate_slow_finish_run_counter_effects boundary frontier buffers positive pointer memory wrap
    publish inputValid strategyRun stateM.good.live.hz accountM
  have intervalM := deflate_slow_finish_run_output_effect boundary frontier buffers positive pointer memory wrap
    publish inputValid strategyRun stateM.good.live.hz accountM
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_common_slow_finish_source boundary.good.live.hz boundary.good.live.hs status low high strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good stateM.good (-1), accountM, effectsM.1, effectsM.2, ?_⟩
    have tailEffect : RawOutputInterval middle (setD middle ds { middleD with last_flush := -1 })
        ob (oo + produced) 0 := .of_same rfl
    simpa only [Nat.add_zero] using intervalM.trans tailEffect
  · subst ret
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good goodS (-1), accountM, effectsM.1, effectsM.2, ?_⟩
    have tailEffect : RawOutputInterval middle
        (setD (setD middle ds { middleD with status := FINISH_STATE }) ds
          { middleD with status := FINISH_STATE, last_flush := -1 }) ob (oo + produced) 0 := .of_same rfl
    simpa only [Nat.add_zero] using intervalM.trans tailEffect
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
    obtain ⟨trailerProduced, after, z', result, trailerRun, goodA, accountA, inputA, outputA, intervalT⟩ :=
      zlib_trailer_output_execution goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have statusEffect : RawOutputInterval middle (setD middle ds { middleD with status := FINISH_STATE })
        ob (oo + produced) 0 := .of_same rfl
    have beforeTrailer : RawOutputInterval h (setD middle ds { middleD with status := FINISH_STATE }) ob oo produced := by
      simpa only [Nat.add_zero] using intervalM.trans statusEffect
    have interval := beforeTrailer.trans intervalT
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, ?_, inputA.trans effectsM.1, ?_, interval⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]


end Zlib.Deflate.Engine.Proofs
