import ZlibF.Proof.«deflate.c.engine.finish-status»

/-! # Public default FINISH dispatch through the actual complete strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The BUSY default data path executes the complete real slow strategy,
records its public status and emits the checksum trailer when ready.
Arbitrary input lengths and every positive raw output capacity are included.
This proves the accepted data path, with its initialized boundary explicit.
The full public entry, call-history invariant, output history and heap
frame are separate obligations; this is not public Goal.deflate. -/
theorem public_busy_slow_finish {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, _endM, buffersM, accountM, _agreesM, _endpointM, _baseM, classification⟩ :=
    deflate_slow_finish_full boundary frontier buffers positive pointer memory wrap output inputValid
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good stateM.good (-1), last_flush_buffers stateM.good buffersM (-1),
      accountM, Or.inl rfl, stateM.bits, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good goodS (-1), last_flush_buffers goodS buffersS (-1),
      accountM, Or.inl rfl, stateM.bits, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    have finished := deflate_slow_finish_run_zero boundary frontier buffers positive pointer memory wrap output
      inputValid strategyRun stateM.good.live.hs (by decide)
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
    obtain ⟨trailerProduced, after, z', result, written, pendingBits, trailerRun, goodA, buffersA, accountA,
      _sizes, _storage, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _trailerBits⟩ :=
      zlib_trailer_publish goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · by_cases queued : result.pending = 0 <;> simp [queued]
    · rw [bitsA]
      decide
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
      exact ⟨by rw [fields], wrapA, inputA, by rw [fields]; exact finished.1, drained, bitsA⟩

end Zlib.Deflate.Engine.Proofs
