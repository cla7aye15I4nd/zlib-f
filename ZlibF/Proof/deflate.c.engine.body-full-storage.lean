import ZlibF.Proof.«deflate.c.engine.decision-full-storage»
import ZlibF.Proof.«deflate.c.engine.no-flush-ready-step»

/-! # Complete object and allocation effects of the actual strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual Z_FINISH body composes refill and decision effects with the full heap and allocation frame. -/
theorem slow_finish_body_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨_accepted, filledHeap, filledZ, filled, _extended, _nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, fieldsF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨shapeF, frameF, _liveF, allocF, nextF⟩ :=
      fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have ownedF : DeflateOwned ds filled = DeflateOwned ds d := by rw [fieldsF]; rfl
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have source := slow_finish_body_after_fill boundary.good.live.hs filledState.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have tested : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok ({ st with brk := true }, filledHeap) := by
        rw [source]
        simp only [empty, beq_self_eq_true, ite_true]
      have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [← eq]
      exact ⟨shapeF, full_private_frame_add_output frameF, full_shape_live_change shapeF, allocF, nextF⟩
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
      have suffix : slowSearchDecision (some (.tab ds)) Z_FINISH st filledHeap = .ok (next, after) := by
        rw [source] at run
        simpa only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] using run
      obtain ⟨shapeD, frameD, _liveD, allocD, nextD⟩ :=
        slow_search_decision_run_full_storage filledState filledEnd filledBuffers nonzero (fun _ => roomF)
          positive pointerF memory (publish.fill fieldsF) suffix
      rw [ownedF] at frameD
      have shape := shapeF.trans shapeD
      have frame := full_frame_trans_shape (full_private_frame_add_output frameF) frameD shapeF
      exact ⟨shape, frame, full_shape_live_change shape, allocD.trans allocF, nextD.trans nextF⟩
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    have suffix : slowSearchDecision (some (.tab ds)) Z_FINISH st h = .ok (next, after) :=
      (slow_ready_body_source boundary.good.live.hs look Z_FINISH st).symm.trans run
    exact slow_search_decision_run_full_storage boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix

/-- The complete actual Z_NO_FLUSH body composes refill and decision effects with the full heap and allocation frame. -/
theorem slow_no_flush_body_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨_accepted, filledHeap, filledZ, filled, _extended, _nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, fieldsF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨shapeF, frameF, _liveF, allocF, nextF⟩ :=
      fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have ownedF : DeflateOwned ds filled = DeflateOwned ds d := by rw [fieldsF]; rfl
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have roomF : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      have suffix : slowSearchDecision (some (.tab ds)) Z_NO_FLUSH st filledHeap = .ok (next, after) :=
        ((slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
          (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)).symm.trans run
      obtain ⟨shapeD, frameD, _liveD, allocD, nextD⟩ :=
        slow_search_decision_run_full_storage filledState filledEnd filledBuffers (by omega) (fun _ => roomF)
          positive pointerF memory (publish.fill fieldsF) suffix
      rw [ownedF] at frameD
      have shape := shapeF.trans shapeD
      have frame := full_frame_trans_shape (full_private_frame_add_output frameF) frameD shapeF
      exact ⟨shape, frame, full_shape_live_change shape, allocD.trans allocF, nextD.trans nextF⟩
    · have tested := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [← eq]
      exact ⟨shapeF, full_private_frame_add_output frameF, full_shape_live_change shapeF, allocF, nextF⟩
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    have suffix : slowSearchDecision (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after) :=
      (slow_ready_body_source boundary.good.live.hs look Z_NO_FLUSH st).symm.trans run
    exact slow_search_decision_run_full_storage boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix

end Zlib.Deflate.Engine.Proofs
