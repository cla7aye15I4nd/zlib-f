import ZlibF.Proof.«deflate.c.engine.full-flush-return»
import ZlibF.Proof.«deflate.c.engine.nonfinal-block-settled»

/-! # Actual complete FULL data path retains the initialized boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete BUSY default FULL data path includes actual slow
compression, marker generation, hash reset, pending publication and retry stores.
It returns and preserves the same initialized content boundary for every
caller output capacity. Public entry and complete histories are separate. -/
theorem public_busy_slow_full_phase {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result extended nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) Z_FULL_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) := by
  have nonzero : Z_FULL_FLUSH ≠ Z_NO_FLUSH := by decide
  have nonfinal : Z_FULL_FLUSH ≠ Z_FINISH := by decide
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, endM, buffersM, accountM, _agreesM, _endpointM, _baseM, classification⟩ :=
    deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_FULL_FLUSH nonzero nonfinal
  have controls := deflate_slow_nonfinal_run_controls boundary frontier buffers positive pointer memory wrap publish
    inputValid Z_FULL_FLUSH nonzero nonfinal strategyRun stateM.good.live.hs
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FULL_FLUSH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_FULL_FLUSH nonzero]
    simp only [bind_app, strategyRun]
  have statusM : middleD.status = BUSY_STATE := controls.status.trans status
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _input, look, symbols⟩
  · subst ret
    have returned := public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_FULL_FLUSH
    have bufferedM := stateM.buffered endM controls.empty_cursor
    exact ⟨used, produced, _, middleZ, _, extended, nextOrigin, middleBase, ys,
      sourceRun.trans returned, last_flush_buffered_boundary bufferedM (-1),
      last_flush_buffers stateM.good buffersM (-1), accountM, statusM, Or.inr rfl⟩
  · subst ret
    have readyM := deflate_slow_nonfinal_run_block_ready boundary frontier buffers positive pointer memory wrap publish
      inputValid Z_FULL_FLUSH nonzero nonfinal strategyRun stateM.good.live.hs
    have available := deflate_slow_nonfinal_run_block_settled boundary frontier buffers positive pointer memory wrap publish
      inputValid Z_FULL_FLUSH nonzero nonfinal strategyRun stateM.good.live.hs
    obtain ⟨pb, buf, treesM, ledger, _balance⟩ := stateM.symbols
    have ysNil : ys = [] := by
      have count := ledger.count
      rw [symbols] at count
      apply List.length_eq_zero_iff.mp
      change 0 = 3 * ys.length at count
      omega
    subst ys
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    obtain ⟨markerProduced, after, z', result, written, remaining, run, stateA, buffersA, accountA,
        _frame, statusA, lastA, _bytes, _pending, _bits⟩ :=
      public_strategy_full_done (stateM.buffered endM controls.empty_cursor)
        buffersM treesM pointerM readyM look available
    refine ⟨used, produced + markerProduced, after, z', result, extended, middleBase, middleBase, [],
      sourceRun.trans run, stateA, buffersA, ?_, statusA.trans statusM, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · rcases lastA with same | retry
      · exact Or.inl (same.trans controls.last_flush)
      · exact Or.inr retry

end Zlib.Deflate.Engine.Proofs
