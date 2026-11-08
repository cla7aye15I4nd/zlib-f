import ZlibF.Proof.«deflate.c.engine.search-ready-step»
import ZlibF.Proof.«deflate.c.engine.finish-strategy-step»

/-! # Complete actual FINISH body at arbitrary output capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual FINISH body includes refill/sliding and all short/full
strategy decisions. Its continuing rank decreases and retains publication readiness even
with zero output capacity. A new loop break means true EOF with no input.
This is one complete body step, not yet the whole FINISH loop. -/
theorem slow_finish_ready_step {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = none → PublishReady result) ∧
      (next.ret = none → next.brk = false → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.brk = true → st.brk = true ∨ (result.lookahead = 0 ∧ z'.avail_in = 0)) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledBoundary, filledFrontier,
        fillAccount, filledBuffers, startF, lookF, agreesF, stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have publishF := publish.fill frameF
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by dsimp only [fillEnd]; omega
    have source := slow_finish_body_after_fill boundary.good.live.hs filledBoundary.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have inputEmpty : filledZ.avail_in = 0 := stoppedF.resolve_left (by rw [empty]; change ¬ 262 ≤ 0; omega)
      refine ⟨used, 0, { st with brk := true }, filledHeap, filledZ, filled, base, xs, extended, nextOrigin,
        ?_, filledBoundary, filledFrontier, filledBuffers, fillAccount, agreesF, endpointF, Nat.le_refl _,
        fun returned => Or.inl returned, Or.inl rfl, fun _ => publishF, ?_, fun _ => Or.inr ⟨empty, inputEmpty⟩⟩
      · rw [source]; simp only [empty, beq_self_eq_true, ite_true]
      · intro _ impossible; cases impossible
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledBoundary.good.live.hs
      obtain ⟨produced, next, after, z', result, base', ys, suffixRun, state, endA, buffersA, accountA,
          _progress, less, endpoint, baseLe, brkA, retA, reasonA, readyA, _continuesA⟩ :=
        slow_search_decision_ready_boundary filledBoundary filledFrontier filledBuffers nonzero
          (fun _ => roomF) positive pointerF memory publishF Z_FINISH st
      have joined : StreamAccounting z z' used produced := by
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans fillAccount accountA
      refine ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
        ?_, state, endA, buffersA, joined, agreesF, ?_, baseLe, reasonA, retA, readyA, ?_, ?_⟩
      · rw [source]; simp only [empty, beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false]; exact suffixRun
      · rw [endpoint]; exact endpointF
      · intro _ _
        have before := fillAccount.2.2.1
        have after := accountA.2.2.1
        omega
      · intro broke; exact Or.inl (brkA.symm.trans broke)
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨produced, next, after, z', result, base', ys, suffixRun, state, endA, buffersA, accountA,
        _progress, less, endpoint, baseLe, brkA, retA, reasonA, readyA, _continuesA⟩ :=
      slow_search_decision_ready_boundary boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_FINISH st
    refine ⟨0, produced, next, after, z', result, base', ys, input, origin, ?_, state, endA, buffersA,
      accountA, fun _ _ => rfl, ?_, baseLe, reasonA, retA, readyA, ?_, ?_⟩
    · have large : ¬ d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt]; exact short
      rw [slow_body_search_decision_source]
      simp only [bind_app, rdD_eq, boundary.good.live.hs, large, ite_false]
      exact suffixRun
    · rw [endpoint, Nat.add_zero]
    · intro _ _
      have count := accountA.2.2.1
      omega
    · intro broke; exact Or.inl (brkA.symm.trans broke)

end Zlib.Deflate.Engine.Proofs
