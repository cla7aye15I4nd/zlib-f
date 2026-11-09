import ZlibF.Proof.«deflate.c.engine.generic-foreign-decision-physical»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual default-memory slow body for every signed flush scalar retains its complete
heap shape, coarse object frame, exact live-object ledger and allocation counters.
Waiting and empty-input exits are included. This is the object footprint; the foreign
owner's non-depth fields and the finer caller BufferFrame require their own conclusions. -/
theorem default_foreign_slow_body_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨_accepted, filledHeap, filledZ, filled, _extended, _nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, fieldsF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨shapeF, frameF, _liveF, allocF, nextF⟩ :=
      fill_window_run_full_storage boundary.toPendingBoundary short wrapD buffers inputValid fillRun
    have finishAtFill (actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, filledHeap)) :
        Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
          LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      rw [← heaps]
      exact ⟨shapeF, full_private_frame_add_output frameF, full_shape_live_change shapeF, allocF, nextF⟩
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    by_cases wait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · have actual : deflate_slow_body (some (.tab ds)) flush st h =
          .ok ({ st with ret := some need_more }, filledHeap) := by
        rw [slow_body_search_decision_source]
        simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
          fillRun, filledState.good.live.hs, wait, ite_true, pure_app]
      have states := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).1
      exact finishAtFill (by simpa only [states] using actual)
    · have notWait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := Bool.eq_false_iff.mpr wait
      by_cases empty : filled.lookahead = 0
      · have notWaitZero : (decide ((0 : UInt32) < MIN_LOOKAHEAD_u) && flush == Z_NO_FLUSH) = false := by
          simpa only [empty] using notWait
        have actual : deflate_slow_body (some (.tab ds)) flush st h =
            .ok ({ st with brk := true }, filledHeap) := by
          rw [slow_body_search_decision_source]
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, empty, notWaitZero, Bool.false_eq_true, ite_false, BEq.rfl, ite_true, pure_app]
        have states := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).1
        exact finishAtFill (by simpa only [states] using actual)
      · have nonzero : 1 ≤ filled.lookahead.toNat := by
          have value : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
        have pointerF : filledZ.next_out = .ref (.dstate_depth owner) oo := by
          rw [fillAccount.2.2.2.2.2.1, advance_zero]
          exact pointer
        have suffix : slowSearchDecision (some (.tab ds)) flush st filledHeap = .ok (next, after) := by
          rw [slow_body_search_decision_source] at run
          simpa only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false,
            beq_eq_false_iff_ne.mpr empty] using run
        obtain ⟨shapeA, frameA, _liveA, allocA, nextA⟩ :=
          default_foreign_slow_search_decision_run_full_storage filledState filledEnd filledBuffers nonzero (fun _ => roomF)
            positive pointerF memory (publish.fill fieldsF) suffix
        have owned : DeflateOwned ds filled = DeflateOwned ds d := by rw [fieldsF]; rfl
        rw [owned] at frameA
        have shape := shapeF.trans shapeA
        exact ⟨shape, full_frame_trans_shape (full_private_frame_add_output frameF) frameA shapeF,
          full_shape_live_change shape, allocA.trans allocF, nextA.trans nextF⟩
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    have suffix := (slow_ready_body_source boundary.good.live.hs ready flush st).symm.trans run
    exact default_foreign_slow_search_decision_run_full_storage boundary frontier buffers (by omega) (fun _ => room)
      positive pointer memory publish suffix

end Zlib.Deflate.Engine.Proofs
