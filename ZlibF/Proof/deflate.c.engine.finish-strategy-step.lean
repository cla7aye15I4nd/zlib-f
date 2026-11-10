import ZlibF.Proof.«deflate.c.engine.fill-end-frontier»
import ZlibF.Proof.«deflate.c.engine.fill-comparison-room»

/-! # Every actual FINISH body preserves the initialized strategy boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Full actual refill supplies the same initialized boundary and the
stronger EOF frontier on one returned heap. -/
theorem fill_window_strategy_end_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (short : d.lookahead.toNat < 262) (wrap : config.wrap = 1)
    (buffers : StreamBuffers h r) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base xs config ∧ EndFrontier after result ∧
      StreamAccounting z z' used 0 ∧ StreamBuffers after r ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, state, account, buffersA,
      startA, lookA, agreesA, stoppedA, frameA⟩ :=
    fill_window_strategy_boundary boundary short wrap buffers inputValid
  have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
  have endA := fill_window_run_end_frontier boundary.toPendingBoundary frontier short wrapD buffers inputValid run state.good.live.hs
  exact ⟨used, after, z', result, extended, nextOrigin, run, state, endA, account, buffersA,
    startA, lookA, agreesA, stoppedA, frameA⟩

/-- Actual FINISH refill stop tests either break at zero lookahead or
execute the proved search/decision suffix on the returned heap. -/
theorem slow_finish_body_after_fill {h filledHeap : Heap} {ds : Nat} {d filled : DeflateState}
    (live : h.dstates ds = some d) (filledLive : filledHeap.dstates ds = some filled)
    (short : d.lookahead.toNat < 262)
    (run : fill_window (some (.tab ds)) h = .ok ((), filledHeap)) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_FINISH st h =
      if filled.lookahead == 0 then .ok ({ st with brk := true }, filledHeap)
      else slowSearchDecision (some (.tab ds)) Z_FINISH st filledHeap := by
  have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
  rw [slow_body_search_decision_source]
  simp only [bind_app, rdD_eq, live, small, ite_true, run, filledLive,
    show (Z_FINISH == Z_NO_FLUSH) = false from rfl, Bool.and_false, Bool.false_eq_true, ite_false]
  by_cases zero : (filled.lookahead == 0) = true <;> simp [zero, pure_app]

/-- Every actual FINISH body includes refill/sliding and all short/full
strategy decisions. Its continuing rank decreases, its output remains
positive, and a new loop break means true EOF with no remaining input.
This is one complete body step, not yet the whole FINISH loop. -/
theorem slow_finish_strategy_step {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = none → next.brk = false → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.brk = true → st.brk = true ∨ (result.lookahead = 0 ∧ z'.avail_in = 0)) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledBoundary, filledFrontier,
        fillAccount, filledBuffers, startF, lookF, agreesF, stoppedF, _frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have outputF : 0 < filledZ.avail_out.toNat := by have count := fillAccount.2.2.2.1; omega
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by dsimp only [fillEnd]; omega
    have source := slow_finish_body_after_fill boundary.good.live.hs filledBoundary.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have inputEmpty : filledZ.avail_in = 0 := stoppedF.resolve_left (by rw [empty]; change ¬ 262 ≤ 0; omega)
      refine ⟨used, 0, { st with brk := true }, filledHeap, filledZ, filled, base, xs, extended, nextOrigin,
        ?_, filledBoundary, filledFrontier, filledBuffers, fillAccount, agreesF, endpointF, Nat.le_refl _,
        fun returned => Or.inl returned, Or.inl rfl, fun _ => outputF, ?_, fun _ => Or.inr ⟨empty, inputEmpty⟩⟩
      · rw [source]; simp only [empty, beq_self_eq_true, ite_true]
      · intro _ impossible; cases impossible
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledBoundary.good.live.hs
      obtain ⟨produced, next, after, z', result, base', ys, suffixRun, state, endA, buffersA, accountA,
          _progress, less, endpoint, baseLe, brkA, retA, reasonA, continuesA⟩ :=
        slow_search_decision_strategy_boundary filledBoundary filledFrontier filledBuffers nonzero
          (fun _ => roomF) positive pointerF memory outputF Z_FINISH st
      have joined : StreamAccounting z z' used produced := by
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans fillAccount accountA
      refine ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
        ?_, state, endA, buffersA, joined, agreesF, ?_, baseLe, reasonA, retA, continuesA, ?_, ?_⟩
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
        _progress, less, endpoint, baseLe, brkA, retA, reasonA, continuesA⟩ :=
      slow_search_decision_strategy_boundary boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory output Z_FINISH st
    refine ⟨0, produced, next, after, z', result, base', ys, input, origin, ?_, state, endA, buffersA,
      accountA, fun _ _ => rfl, ?_, baseLe, reasonA, retA, continuesA, ?_, ?_⟩
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
