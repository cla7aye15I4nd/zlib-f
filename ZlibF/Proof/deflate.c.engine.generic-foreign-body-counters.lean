import ZlibF.Proof.«deflate.c.engine.generic-foreign-decision-counters»
import ZlibF.Proof.«deflate.c.engine.fill-counters»
import ZlibF.Proof.«deflate.c.engine.no-flush-ready-step»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete real FINISH and NO_FLUSH bodies compose the actual refill counters
with the actual foreign publication counters, including waiting and empty input. -/
theorem default_foreign_slow_finish_body_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillEffects := fill_window_run_counter_effects boundary.toPendingBoundary short wrapD buffers inputValid
      fillRun filledState.good.live.hz fillAccount
    have source := slow_finish_body_after_fill boundary.good.live.hs filledState.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h =
          .ok ({ st with brk := true }, filledHeap) := by
        rw [source]
        simp only [empty, beq_self_eq_true, ite_true]
      have same := actual_run_stream_unique actualRun run filledState.good.live.hz live
      exact stream_counter_effects_identify same fillAccount account fillEffects.1 (by simpa using fillEffects.2)
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have pointerF : filledZ.next_out = .ref (.dstate_depth owner) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
        default_foreign_slow_search_decision_counter_execution filledState filledEnd filledBuffers nonzero roomF
          positive pointerF memory (publish.fill frameF) Z_FINISH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (expected, other) := by
        rw [source]
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false]
        exact suffix
      have same := actual_run_stream_unique actualRun run goodE.live.hz live
      have combined := stream_accounting_trans fillAccount accountE
      have effects := stream_counter_effects_trans (used := accepted) (first := 0) (produced := 0) (second := delivered) fillEffects.1 (by simpa using fillEffects.2)
        (by simpa using inputE) outputE
      exact stream_counter_effects_identify same combined account effects.1 effects.2
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
      default_foreign_slow_search_decision_counter_execution boundary frontier buffers (by omega) room
        positive pointer memory publish Z_FINISH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_FINISH st).trans suffix
    have same := actual_run_stream_unique actualRun run goodE.live.hz live
    exact stream_counter_effects_identify same accountE account (by simpa using inputE) outputE

/-- Actual NO_FLUSH refills, waits and ready decisions retain exact totals. -/
theorem default_foreign_slow_no_flush_body_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillEffects := fill_window_run_counter_effects boundary.toPendingBoundary short wrapD buffers inputValid
      fillRun filledState.good.live.hz fillAccount
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have roomF : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      have pointerF : filledZ.next_out = .ref (.dstate_depth owner) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
        default_foreign_slow_search_decision_counter_execution filledState filledEnd filledBuffers (by omega) roomF
          positive pointerF memory (publish.fill frameF) Z_NO_FLUSH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (expected, other) := by
        exact ((slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
          (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)).trans suffix
      have same := actual_run_stream_unique actualRun run goodE.live.hz live
      have combined := stream_accounting_trans fillAccount accountE
      have effects := stream_counter_effects_trans (used := accepted) (first := 0) (produced := 0) (second := delivered) fillEffects.1 (by simpa using fillEffects.2)
        (by simpa using inputE) outputE
      exact stream_counter_effects_identify same combined account effects.1 effects.2
    · have actualRun := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have same := actual_run_stream_unique actualRun run filledState.good.live.hz live
      exact stream_counter_effects_identify same fillAccount account fillEffects.1 (by simpa using fillEffects.2)
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
      default_foreign_slow_search_decision_counter_execution boundary frontier buffers (by omega) room
        positive pointer memory publish Z_NO_FLUSH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_NO_FLUSH st).trans suffix
    have same := actual_run_stream_unique actualRun run goodE.live.hz live
    exact stream_counter_effects_identify same accountE account (by simpa using inputE) outputE


end Zlib.Deflate.Engine.Proofs
