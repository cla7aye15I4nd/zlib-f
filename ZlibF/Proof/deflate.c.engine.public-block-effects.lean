import ZlibF.Proof.«deflate.c.engine.public-slow-block»
import ZlibF.Proof.«deflate.c.engine.nonfinal-call-effects»

/-! # Exact counters and storage effects through actual public BLOCK return -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual default BLOCK dispatch and its public return retain the exact
output interval, wrapping totals and heap/allocation frame. This is the
BUSY data cutpoint; complete public entry and histories remain separate. -/
theorem public_busy_slow_block_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, _endM, buffersM, accountM, _agreesM, _endpointM, _baseM, classification⟩ :=
    deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_BLOCK (by decide) (by decide)
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_BLOCK (by decide)]
    simp only [bind_app, strategyRun]
  obtain ⟨inputM, outputM, intervalM, shapeM, frameM, liveM, allocM, nextM⟩ :=
    deflate_slow_nonfinal_run_effects boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_BLOCK (by decide) (by decide) strategyRun stateM.good.live.hz accountM
  have stopped : publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle =
      .ok (Z_OK, setD middle ds { middleD with last_flush := -1 }) →
      ∃ used produced after z' result,
        publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
        DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
        z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
        RawOutputInterval h after ob oo produced ∧
        Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
        LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
    intro run
    have shapeD := shape_setD stateM.good.live.hs { middleD with last_flush := -1 }
    have frameD : Frame middle (setD middle ds { middleD with last_flush := -1 })
        (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
      full_frame_weaken (state_store_full_frame middle ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
    have shape := shapeM.trans shapeD
    have interval : RawOutputInterval h (setD middle ds { middleD with last_flush := -1 }) ob oo produced := by
      have store : RawOutputInterval middle (setD middle ds { middleD with last_flush := -1 }) ob (oo + produced) 0 := .of_same rfl
      simpa only [Nat.add_zero] using intervalM.trans store
    exact ⟨used, produced, _, middleZ, _, sourceRun.trans run,
      last_flush_good stateM.good (-1), last_flush_buffers stateM.good buffersM (-1),
      accountM, inputM, outputM, interval, shape, full_frame_trans_shape frameM frameD shapeM,
      full_shape_live_change shape, allocM, nextM⟩
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _input, _look, _symbols⟩
  · subst ret
    exact stopped (public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_BLOCK)
  · subst ret
    have readyM := deflate_slow_nonfinal_run_block_ready boundary frontier buffers positive pointer memory wrap publish
      inputValid Z_BLOCK (by decide) (by decide) strategyRun stateM.good.live.hs
    have run := public_strategy_block_done_ready stateM.good readyM
    by_cases exhausted : (middleZ.avail_out == 0) = true
    · exact stopped (by simpa only [exhausted, ite_true] using run)
    · refine ⟨used, produced, middle, middleZ, middleD, sourceRun.trans ?_, stateM.good,
        buffersM, accountM, inputM, outputM, intervalM, shapeM, frameM, liveM, allocM, nextM⟩
      simpa only [exhausted, Bool.false_eq_true, ite_false] using run

end Zlib.Deflate.Engine.Proofs
