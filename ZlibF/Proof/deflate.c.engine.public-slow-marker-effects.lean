import ZlibF.Proof.«deflate.c.engine.marker-return-effects»
import ZlibF.Proof.«deflate.c.engine.nonfinal-call-effects»
import ZlibF.Proof.«deflate.c.engine.nonfinal-block-settled»

/-! # Complete actual marker data paths have exact public effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual default PARTIAL/SYNC/FULL dispatch and its public return retain the exact
output interval, wrapping totals and heap/allocation frame. This is the
BUSY data cutpoint; complete public entry and histories remain separate. -/
theorem public_busy_slow_marker_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) flush h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have nonzero : flush ≠ Z_NO_FLUSH := by rcases flag with rfl | rfl | rfl <;> decide
  have nonfinal : flush ≠ Z_FINISH := by rcases flag with rfl | rfl | rfl <;> decide
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, endM, buffersM, accountM, _agreesM, _endpointM, _baseM, classification⟩ :=
    deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      flush nonzero nonfinal
  have sourceRun : publicDataTail (some r) (some (.tab ds)) flush h =
      publicStrategyReturn (some r) (some (.tab ds)) flush ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy flush nonzero]
    simp only [bind_app, strategyRun]
  obtain ⟨inputM, outputM, intervalM, shapeM, frameM, liveM, allocM, nextM⟩ :=
    deflate_slow_nonfinal_run_effects boundary frontier buffers positive pointer memory wrap publish inputValid
      flush nonzero nonfinal strategyRun stateM.good.live.hz accountM
  have stopped : publicStrategyReturn (some r) (some (.tab ds)) flush ret middle =
      .ok (Z_OK, setD middle ds { middleD with last_flush := -1 }) →
      ∃ used produced after z' result,
        publicDataTail (some r) (some (.tab ds)) flush h = .ok (Z_OK, after) ∧
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
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _input, look, symbols⟩
  · subst ret
    exact stopped (public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted flush)
  · subst ret
    have readyM := deflate_slow_nonfinal_run_block_ready boundary frontier buffers positive pointer memory wrap publish
      inputValid flush nonzero nonfinal strategyRun stateM.good.live.hs
    have available := deflate_slow_nonfinal_run_block_settled boundary frontier buffers positive pointer memory wrap publish
      inputValid flush nonzero nonfinal strategyRun stateM.good.live.hs
    obtain ⟨pb, buf, treesM, ledger, _balance⟩ := stateM.symbols
    have ysNil : ys = [] := by
      have count := ledger.count
      rw [symbols] at count
      apply List.length_eq_zero_iff.mp
      change 0 = 3 * ys.length at count
      omega
    subst ys
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]; rfl
    obtain ⟨markerProduced, after, z', result, run, goodA, buffersA, accountA, inputA, outputA,
        intervalA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
      public_strategy_marker_done_effects (stateM.buffered endM (fun _ => readyM.2.1)) buffersM treesM
        pointerM readyM look available flush flag
    have configM : ConfigFrame d middleD := Eq.trans stateM.configuration boundary.configuration.symm
    have frameA' : Frame middle after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
      apply full_frame_weaken frameA
      intro b changed
      rcases changed with root | owned | output
      · exact Or.inl root
      · rw [configM.owned] at owned
        exact Or.inr (Or.inl owned)
      · exact Or.inr (Or.inr output)
    have totals := stream_counter_effects_trans (first := 0) inputM outputM (by simpa using inputA) outputA
    have shape := shapeM.trans shapeA
    refine ⟨used, produced + markerProduced, after, z', result, sourceRun.trans run,
      goodA, buffersA, ?_, ?_, totals.2, intervalM.trans intervalA, shape,
      full_frame_trans_shape frameM frameA' shapeM, full_shape_live_change shape,
      allocA.trans allocM, nextA.trans nextM⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · simpa only [Nat.add_zero] using totals.1

end Zlib.Deflate.Engine.Proofs
