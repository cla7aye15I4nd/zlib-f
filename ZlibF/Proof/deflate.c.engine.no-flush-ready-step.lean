import ZlibF.Proof.«deflate.c.engine.no-flush-body-controls»

/-! # Actual NO_FLUSH body execution at arbitrary prepared output capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real ready body skips refill for every flag. -/
theorem slow_ready_body_source {h : Heap} {ds : Nat} {d : DeflateState}
    (live : h.dstates ds = some d) (look : 262 ≤ d.lookahead.toNat) (flush : Int32) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) flush st h = slowSearchDecision (some (.tab ds)) flush st h := by
  have large : ¬ d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt]; exact Nat.not_lt.mpr look
  rw [slow_body_search_decision_source]
  simp only [bind_app, rdD_eq, live, large, ite_false]

/-- A complete actual NO_FLUSH body at a publication-ready entry includes
zero raw output. Its continuing state is again publication-ready and its
rank decreases, including real refill and full block output. -/
theorem slow_no_flush_ready_step {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      next.brk = st.brk ∧ (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = none → PublishReady result) ∧
      (next.ret = none → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨
        ((z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0)) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, startF, lookF, agreesF, stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by dsimp only [fillEnd]; omega
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have room : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      obtain ⟨produced, next, after, z', result, base', ys, suffixRun, stateA, endA, buffersA, accountA,
          _progress, less, endpoint, baseLe, brkA, retA, reasonA, readyA, _continuesA⟩ :=
        slow_search_decision_ready_boundary filledState filledEnd filledBuffers (by omega) (fun _ => room)
          positive pointerF memory (publish.fill frameF) Z_NO_FLUSH st
      have source := (slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
        (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)
      have joined : StreamAccounting z z' used produced := by
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans fillAccount accountA
      refine ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
        source.trans suffixRun, stateA, endA, buffersA, joined, agreesF, ?_, baseLe, brkA, retA, readyA, ?_, ?_⟩
      · rw [endpoint]; exact endpointF
      · intro running
        have before := fillAccount.2.2.1
        have after := accountA.2.2.1
        have decrease := less
        omega
      · intro returned
        rcases reasonA returned with old | empty
        · exact Or.inl old
        · exact Or.inr (Or.inr empty)
    · have shortF : filled.lookahead.toNat < 262 := by omega
      have inputEmpty : filledZ.avail_in = 0 := stoppedF.resolve_left ready
      refine ⟨used, 0, { st with ret := some need_more }, filledHeap, filledZ, filled, base, xs, extended, nextOrigin,
        slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short shortF fillRun st,
        filledState, filledEnd, filledBuffers, fillAccount, agreesF, endpointF, Nat.le_refl _, rfl, Or.inr rfl,
        ?_, ?_, fun _ => Or.inr (Or.inl ⟨inputEmpty, shortF⟩)⟩
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨produced, next, after, z', result, base', ys, suffixRun, stateA, endA, buffersA, accountA,
        _progress, less, endpoint, baseLe, brkA, retA, reasonA, readyA, _continuesA⟩ :=
      slow_search_decision_ready_boundary boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_NO_FLUSH st
    refine ⟨0, produced, next, after, z', result, base', ys, input, origin,
      (slow_ready_body_source boundary.good.live.hs ready Z_NO_FLUSH st).trans suffixRun,
      stateA, endA, buffersA, accountA, fun _ _ => rfl, ?_, baseLe, brkA, retA, readyA, ?_, ?_⟩
    · rw [endpoint, Nat.add_zero]
    · intro running
      have count := accountA.2.2.1
      have decrease := less
      omega
    · intro returned
      rcases reasonA returned with old | empty
      · exact Or.inl old
      · exact Or.inr (Or.inr empty)

end Zlib.Deflate.Engine.Proofs
