import ZlibF.Proof.«deflate.c.engine.slow-body-loop»
import ZlibF.Proof.«deflate.c.engine.loop-accounting»

/-! # Real refill and full ready decisions share the strategy boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Refill, pending insertion, sliding and padding retain configuration
and the publication phase. Exact input accounting transfers the condition
on remaining caller output to the same returned stream. -/
theorem fill_window_strategy_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (short : d.lookahead.toNat < 262) (wrap : config.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base xs config ∧
      StreamAccounting z z' used 0 ∧ StreamBuffers after r ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  have wrapEq : d.wrap = config.wrap := congrArg EngineConfig.wrap boundary.configuration
  obtain ⟨used, after, z', result, extended, nextOrigin, run, state, account, buffersA, _storage,
    startA, lookA, _wrapA, _originA, agreesA, stoppedA, frameA⟩ :=
    fill_window_content_buffers boundary.toContentBoundary short (wrapEq.trans wrap) buffers inputValid
  have configA := ConfigFrame.fill frameA
  have lowA : result.bi_valid.toInt < 8 := by rw [frameA]; exact boundary.bits
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by rw [frameA]; exact boundary.strict
  have phaseA : 0 < z'.avail_out.toNat → PublishReady result := by
    intro space
    have count := account.2.2.2.1
    exact PublishReady.fill (boundary.resume (by omega)) frameA
  exact ⟨used, after, z', result, extended, nextOrigin, run,
    ⟨state, Eq.trans configA boundary.configuration, boundary.clear.fill frameA, lowA, strictA, phaseA⟩,
    account, buffersA, startA, lookA, agreesA, stoppedA, frameA⟩

set_option maxHeartbeats 2000000 in
/-- One complete actual NO_FLUSH body, with every admitted refill and
full-buffer decision. If it continues, available input plus lookahead
strictly decreases and caller output remains positive. This is the
numerical and state preservation step for the full strategy loop. -/
theorem slow_no_flush_strategy_step {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (positive : 0 < config.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      next.brk = st.brk ∧ (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = none → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨
        ((z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0)) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState,
      fillAccount, filledBuffers, startF, lookF, agreesF, _stoppedF, _frameF⟩ :=
      fill_window_strategy_boundary boundary short wrap buffers inputValid
    have outputF : 0 < filledZ.avail_out.toNat := by have count := fillAccount.2.2.2.1; omega
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by
      dsimp only [fillEnd]
      omega
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · obtain ⟨produced, next, after, z', result, base', ys, bodyRun, state, buffersA, bodyAccount,
        _progress, less, endpoint, baseLe, brkA, retA, continuedA, reasonA⟩ :=
        slow_body_strategy_boundary filledState filledBuffers positive pointerF memory outputF ready Z_NO_FLUSH st
      have prefixRun := slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st
      have joined : StreamAccounting z z' used produced := by
        simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans fillAccount bodyAccount
      refine ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
        prefixRun.trans bodyRun, state, buffersA, joined, agreesF, ?_, baseLe, brkA, retA, continuedA, ?_, ?_⟩
      · rw [endpoint]
        exact endpointF
      · intro _
        have before := fillAccount.2.2.1
        have after := bodyAccount.2.2.1
        omega
      · intro returned
        rcases reasonA returned with old | empty
        · exact Or.inl old
        · exact Or.inr (Or.inr empty)
    · have shortF : filled.lookahead.toNat < 262 := by omega
      have inputEmpty : filledZ.avail_in = 0 := _stoppedF.resolve_left ready
      refine ⟨used, 0, { st with ret := some need_more }, filledHeap, filledZ, filled, base, xs, extended, nextOrigin,
        slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short shortF fillRun st,
        filledState, filledBuffers, fillAccount, agreesF, endpointF, Nat.le_refl _, rfl, Or.inr rfl, ?_, ?_, ?_⟩
      · intro impossible; cases impossible
      · intro impossible; cases impossible
      · intro _; exact Or.inr (Or.inl ⟨inputEmpty, shortF⟩)
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    obtain ⟨produced, next, after, z', result, base', ys, run, state, buffersA, account,
      _progress, less, endpoint, baseLe, brkA, retA, continuedA, reasonA⟩ :=
      slow_body_strategy_boundary boundary buffers positive pointer memory output ready Z_NO_FLUSH st
    refine ⟨0, produced, next, after, z', result, base', ys, input, origin, run, state, buffersA, account,
      fun _ _ => rfl, ?_, baseLe, brkA, retA, continuedA, ?_, ?_⟩
    · rw [endpoint, Nat.add_zero]
    · intro _
      have same := account.2.2.1
      omega
    · intro returned
      rcases reasonA returned with old | empty
      · exact Or.inl old
      · exact Or.inr (Or.inr empty)

end Zlib.Deflate.Engine.Proofs
