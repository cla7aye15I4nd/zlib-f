import ZlibF.Proof.«deflate.c.engine.finish-body-controls»

/-! # Actual NO_FLUSH bodies retain the EOF frontier and public controls -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- At full lookahead the actual body directly executes its search/decision suffix. -/
theorem slow_ready_body_run_end_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (look : 262 ≤ d.lookahead.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (publish : PublishReady d)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) : EndFrontier after result ∧ StrategyControls d result := by
  have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
    have range := boundary.range
    dsimp only [fillEnd] at range
    omega
  have large : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    exact Nat.not_lt.mpr look
  have suffix : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after) := by
    rw [slow_body_search_decision_source] at run
    simpa only [bind_app, rdD_eq, boundary.good.live.hs, large, ite_false] using run
  have controls := slow_search_decision_run_controls boundary frontier buffers (by omega) (fun _ => room)
    positive pointer memory publish suffix live
  obtain ⟨_produced, expected, other, _z', result', _base', _ys, expectedRun, stateA, endA, _rest⟩ :=
    slow_search_decision_ready_boundary boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish flush st
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (expectedRun.symm.trans suffix))).2
  have states : result' = result := by
    have state := live
    rw [← heaps] at state
    exact Option.some.inj (stateA.good.live.hs.symm.trans state)
  subst other result'
  exact ⟨endA, controls⟩

/-- Actual NO_FLUSH refill either waits with the filled frontier or executes
that same complete ready body. Both return the control and EOF frontier. -/
theorem slow_no_flush_body_run_end_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
    (live : after.dstates ds = some result) : EndFrontier after result ∧ StrategyControls d result := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨_used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have publishF := publish.fill frameF
    have controlsF := StrategyControls.fill publish frameF
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have source := slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have actual : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st filledHeap = .ok (next, after) := source.symm.trans run
      obtain ⟨endA, controlsA⟩ := slow_ready_body_run_end_controls filledState filledEnd filledBuffers ready
        positive pointerF memory publishF actual live
      exact ⟨endA, controlsA.empty_cursor, controlsA.status.trans controlsF.status, controlsA.last_flush.trans controlsF.last_flush⟩
    · have source := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have heaps : filledHeap = after := (Prod.mk.inj (Except.ok.inj (source.symm.trans run))).2
      have states : filled = result := by
        have state := live
        rw [← heaps] at state
        exact Option.some.inj (filledState.good.live.hs.symm.trans state)
      subst filledHeap filled
      exact ⟨filledEnd, controlsF⟩
  · exact slow_ready_body_run_end_controls boundary frontier buffers (by omega) positive pointer memory publish run live

end Zlib.Deflate.Engine.Proofs
