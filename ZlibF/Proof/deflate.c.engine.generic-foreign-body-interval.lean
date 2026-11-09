import ZlibF.Proof.«deflate.c.engine.generic-foreign-decision-interval»
import ZlibF.Proof.«deflate.c.engine.body-counters»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual generic search producer supplies its own actual interval refinement;
no effect contract is assumed by this execution constructor. -/
theorem default_foreign_slow_search_interval_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1≤d.lookahead.toNat)
    (room : d.strstart.toNat+262≤d.window_size.toNat)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (ready : PublishReady d) (flush : Int32) (st : LoopS) :
    ∃ produced next after z' result,
      slowSearchDecision (some (.tab ds)) flush st h=.ok (next,after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨produced,next,after,z',result,_base,_ys,_before,_written,_remaining,run,stateA,
    _endA,_buffersA,accountA,_rest⟩ :=
    default_foreign_slow_search_decision_strategy_encoding boundary frontier buffers lookahead room positive pointer memory ready flush st
  exact ⟨produced,next,after,z',result,run,stateA.good,accountA,
    default_foreign_slow_search_decision_run_output_interval boundary frontier buffers lookahead (fun _=>room)
      positive pointer memory ready run stateA.good.live.hz accountA⟩

theorem default_foreign_slow_finish_body_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillStorage := fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have fillEffect : ByteOutputInterval h filledHeap (.dstate_depth owner) oo 0 :=
      .of_foreign_private_frame boundary.good buffers pointer fillStorage.2.1
    have source := slow_finish_body_after_fill boundary.good.live.hs filledState.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h =
          .ok ({ st with brk := true }, filledHeap) := by
        rw [source]
        simp only [empty, beq_self_eq_true, ite_true]
      have heaps := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
      rw [← heaps]
      exact ByteOutputInterval.of_foreign_private_frame boundary.good buffers pointer fillStorage.2.1
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have pointerF : filledZ.next_out = .ref (.dstate_depth owner) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, suffixEffect⟩ :=
        default_foreign_slow_search_interval_execution filledState filledEnd filledBuffers nonzero roomF
          positive pointerF memory (publish.fill frameF) Z_FINISH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (expected, other) := by
        rw [source]
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false]
        exact suffix
      have combined : StreamAccounting z ze accepted delivered := by
        simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans fillAccount accountE
      have joined : ByteOutputInterval h other (.dstate_depth owner) oo delivered := by
        simpa only [Nat.zero_add] using fillEffect.trans suffixEffect
      exact ByteOutputInterval.identify actualRun run goodE.live.hz live combined account joined
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, suffixEffect⟩ :=
      default_foreign_slow_search_interval_execution boundary frontier buffers (by omega) room
        positive pointer memory publish Z_FINISH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_FINISH st).trans suffix
    have effect := suffixEffect
    exact ByteOutputInterval.identify actualRun run goodE.live.hz live accountE account effect

/-- The real NO_FLUSH body includes private refill, waiting and exact decision output intervals. -/
theorem default_foreign_slow_no_flush_body_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have fillStorage := fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have fillEffect : ByteOutputInterval h filledHeap (.dstate_depth owner) oo 0 :=
      .of_foreign_private_frame boundary.good buffers pointer fillStorage.2.1
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have roomF : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      have pointerF : filledZ.next_out = .ref (.dstate_depth owner) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, suffixEffect⟩ :=
        default_foreign_slow_search_interval_execution filledState filledEnd filledBuffers (by omega) roomF
          positive pointerF memory (publish.fill frameF) Z_NO_FLUSH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (expected, other) := by
        exact ((slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
          (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)).trans suffix
      have combined : StreamAccounting z ze accepted delivered := by
        simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans fillAccount accountE
      have joined : ByteOutputInterval h other (.dstate_depth owner) oo delivered := by
        simpa only [Nat.zero_add] using fillEffect.trans suffixEffect
      exact ByteOutputInterval.identify actualRun run goodE.live.hz live combined account joined
    · have actualRun := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have heaps := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
      rw [← heaps]
      exact ByteOutputInterval.of_foreign_private_frame boundary.good buffers pointer fillStorage.2.1
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, suffixEffect⟩ :=
      default_foreign_slow_search_interval_execution boundary frontier buffers (by omega) room
        positive pointer memory publish Z_NO_FLUSH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_NO_FLUSH st).trans suffix
    have effect := suffixEffect
    exact ByteOutputInterval.identify actualRun run goodE.live.hz live accountE account effect

end Zlib.Deflate.Engine.Proofs
