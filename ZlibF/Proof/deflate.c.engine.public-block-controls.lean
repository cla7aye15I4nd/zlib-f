import ZlibF.Proof.«deflate.c.engine.public-block-buffer-frame»

/-! # Public BLOCK return retains the caller-independent empty cursor -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual BLOCK data execution retains the empty pending cursor even if
the caller's output is exhausted. This permits later legal rebuffering. -/
theorem public_busy_slow_block_run_empty_cursor {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {rc : Int32} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (rc, after))
    (live : after.dstates ds = some result) : result.pending = 0 → result.pending_out = result.pending_buf := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, _endM, _buffersM, _accountM, _agreesM, _endpointM, _baseM, classification⟩ :=
    deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_BLOCK (by decide) (by decide)
  have controls := deflate_slow_nonfinal_run_controls boundary frontier buffers positive pointer memory wrap publish
    inputValid Z_BLOCK (by decide) (by decide) strategyRun stateM.good.live.hs
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_BLOCK (by decide)]
    simp only [bind_app, strategyRun]
  have stopped : publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle =
      .ok (Z_OK, setD middle ds { middleD with last_flush := -1 }) →
      result.pending = 0 → result.pending_out = result.pending_buf := by
    intro returned
    have actual := sourceRun.trans returned
    have heaps : setD middle ds { middleD with last_flush := -1 } = after :=
      (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps] at live
    have states : { middleD with last_flush := -1 } = result := by
      simpa only [setD_dstates_same, Option.some.injEq] using live
    rw [← states]
    exact controls.empty_cursor
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _input, _look, _symbols⟩
  · subst ret
    exact stopped (public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_BLOCK)
  · subst ret
    have readyM := deflate_slow_nonfinal_run_block_ready boundary frontier buffers positive pointer memory wrap publish
      inputValid Z_BLOCK (by decide) (by decide) strategyRun stateM.good.live.hs
    have returned := public_strategy_block_done_ready stateM.good readyM
    by_cases exhausted : (middleZ.avail_out == 0) = true
    · exact stopped (by simpa only [exhausted, ite_true] using returned)
    · have actual : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, middle) :=
        sourceRun.trans (by simpa only [exhausted, Bool.false_eq_true, ite_false] using returned)
      have heaps : middle = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      rw [← heaps] at live
      have states : middleD = result := Option.some.inj (stateM.good.live.hs.symm.trans live)
      rw [← states]
      exact controls.empty_cursor

end Zlib.Deflate.Engine.Proofs
