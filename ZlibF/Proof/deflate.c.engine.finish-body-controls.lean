import ZlibF.Proof.«deflate.c.engine.search-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»

/-! # Every actual FINISH body retains the public controls -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real refill, EOF stops and every search/decision branch retain the
cursor phase, status and last flush request on the same return heap. -/
theorem slow_finish_body_run_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledBoundary, filledFrontier,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have sourceEq := slow_finish_body_after_fill boundary.good.live.hs filledBoundary.good.live.hs short fillRun st
    have publishF := publish.fill frameF
    have controlsF := StrategyControls.fill publish frameF
    by_cases empty : filled.lookahead = 0
    · have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h =
          .ok ({ st with brk := true }, filledHeap) := by
        rw [sourceEq]
        simp only [empty, beq_self_eq_true, ite_true]
      have heaps : filledHeap = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
      have states : filled = result := by
        have hs := live
        rw [← heaps] at hs
        exact Option.some.inj (filledBoundary.good.live.hs.symm.trans hs)
      rw [← states]
      exact controlsF
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledBoundary.good.live.hs
      have suffix : slowSearchDecision (some (.tab ds)) Z_FINISH st filledHeap = .ok (next, after) := by
        rw [sourceEq] at run
        simpa only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] using run
      have controls := slow_search_decision_run_controls filledBoundary filledFrontier filledBuffers nonzero
        (fun _ => roomF) positive pointerF memory publishF suffix live
      exact ⟨controls.empty_cursor, controls.status.trans controlsF.status, controls.last_flush.trans controlsF.last_flush⟩
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    have large : ¬ d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt]; exact short
    have suffix : slowSearchDecision (some (.tab ds)) Z_FINISH st h = .ok (next, after) := by
      rw [slow_body_search_decision_source] at run
      simpa only [bind_app, rdD_eq, boundary.good.live.hs, large, ite_false] using run
    exact slow_search_decision_run_controls boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix live

end Zlib.Deflate.Engine.Proofs
