import ZlibF.Proof.«deflate.c.engine.decision-output-interval»
import ZlibF.Proof.«deflate.c.engine.body-counters»

/-! # Exact raw caller output intervals through actual strategy execution -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real FINISH body composes private refill with the exact decision output interval. -/
theorem slow_finish_body_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillStorage := fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have fillEffect : RawOutputInterval h filledHeap ob oo 0 :=
      .of_private_frame boundary.good buffers pointer fillStorage.2.1
    have source := slow_finish_body_after_fill boundary.good.live.hs filledState.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h =
          .ok ({ st with brk := true }, filledHeap) := by
        rw [source]
        simp only [empty, beq_self_eq_true, ite_true]
      have heaps := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
      rw [← heaps]
      exact RawOutputInterval.of_private_frame boundary.good buffers pointer fillStorage.2.1
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
        slow_search_decision_counter_execution filledState filledEnd filledBuffers nonzero (fun _ => roomF)
          positive pointerF memory (publish.fill frameF) Z_FINISH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (expected, other) := by
        rw [source]
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false]
        exact suffix
      have suffixEffect := slow_search_decision_run_output_effect filledState filledEnd filledBuffers
        (by omega) (fun _ => roomF) positive pointerF memory (publish.fill frameF) suffix goodE.live.hz accountE
      have combined : StreamAccounting z ze accepted delivered := by
        simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans fillAccount accountE
      have joined : RawOutputInterval h other ob oo delivered := by
        simpa only [Nat.zero_add] using fillEffect.trans suffixEffect
      exact RawOutputInterval.identify actualRun run goodE.live.hz live combined account joined
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
      slow_search_decision_counter_execution boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_FINISH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_FINISH st).trans suffix
    have effect := slow_search_decision_run_output_effect boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix goodE.live.hz accountE
    exact RawOutputInterval.identify actualRun run goodE.live.hz live accountE account effect

/-- The real NO_FLUSH body includes private refill, waiting and exact decision output intervals. -/
theorem slow_no_flush_body_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillStorage := fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have fillEffect : RawOutputInterval h filledHeap ob oo 0 :=
      .of_private_frame boundary.good buffers pointer fillStorage.2.1
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have roomF : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
        slow_search_decision_counter_execution filledState filledEnd filledBuffers (by omega) (fun _ => roomF)
          positive pointerF memory (publish.fill frameF) Z_NO_FLUSH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (expected, other) := by
        exact ((slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
          (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)).trans suffix
      have suffixEffect := slow_search_decision_run_output_effect filledState filledEnd filledBuffers
        (by omega) (fun _ => roomF) positive pointerF memory (publish.fill frameF) suffix goodE.live.hz accountE
      have combined : StreamAccounting z ze accepted delivered := by
        simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans fillAccount accountE
      have joined : RawOutputInterval h other ob oo delivered := by
        simpa only [Nat.zero_add] using fillEffect.trans suffixEffect
      exact RawOutputInterval.identify actualRun run goodE.live.hz live combined account joined
    · have actualRun := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have heaps := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
      rw [← heaps]
      exact RawOutputInterval.of_private_frame boundary.good buffers pointer fillStorage.2.1
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, inputE, outputE⟩ :=
      slow_search_decision_counter_execution boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_NO_FLUSH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_NO_FLUSH st).trans suffix
    have effect := slow_search_decision_run_output_effect boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix goodE.live.hz accountE
    exact RawOutputInterval.identify actualRun run goodE.live.hz live accountE account effect

end Zlib.Deflate.Engine.Proofs
