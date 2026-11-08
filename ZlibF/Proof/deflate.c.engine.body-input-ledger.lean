import ZlibF.Proof.«deflate.c.engine.fill-input-ledger»
import ZlibF.Proof.«deflate.c.engine.body-checksum»
import ZlibF.Proof.«deflate.c.engine.body-encoding»

/-! # Actual bodies append precisely their consumed caller bytes to logical input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual signed-flush body extends logical input by exactly its
consumed original caller bytes. Whole refill/search/decision executions
identify the same returned boundary. This is a byte-list equality and
assumes neither a checksum property nor a callee execution contract. -/
theorem slow_body_run_input_ledger {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced nextOrigin nextBase : Nat}
    {z returned : ZStream} {d result : DeflateState} {xs ys : List Symbol}
    {input extended : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (stateA : StrategyBoundary after r ds returned result extended nextOrigin nextBase ys config)
    (account : StreamAccounting z returned used produced)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i)
    (endpoint : nextOrigin + fillEnd result = origin + fillEnd d + used) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      inputPrefix extended (nextOrigin + fillEnd result) = inputPrefix input (origin + fillEnd d) ++ copied := by
  have identify {other : Heap} {otherZ : ZStream} {otherD : DeflateState}
      {otherInput : Nat → UInt8} {otherOrigin otherBase accepted delivered : Nat}
      {otherYs : List Symbol} {expected : LoopS}
      (actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (expected, other))
      (state : StrategyBoundary other r ds otherZ otherD otherInput otherOrigin otherBase otherYs config)
      (counts : StreamAccounting z otherZ accepted delivered)
      (agrees : ∀ i, i < origin + fillEnd d → otherInput i = input i)
      (endEq : otherOrigin + fillEnd otherD = origin + fillEnd d + accepted)
      (covered : otherOrigin ≤ origin + fillEnd d)
      (ledger : ∃ copied, Bytes h z.next_in accepted copied ∧ copied.length = accepted ∧
        inputPrefix otherInput (otherOrigin + fillEnd otherD) = inputPrefix input (origin + fillEnd d) ++ copied) :
      ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      inputPrefix extended (nextOrigin + fillEnd result) = inputPrefix input (origin + fillEnd d) ++ copied := by
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst other
    have streams : otherZ = returned := Option.some.inj (state.good.live.hz.symm.trans stateA.good.live.hz)
    have states : otherD = result := Option.some.inj (state.good.live.hs.symm.trans stateA.good.live.hs)
    subst otherZ otherD
    have acceptedEq := (stream_accounting_counts_unique counts account).1
    have origins : otherOrigin = nextOrigin := by omega
    subst otherOrigin
    have sameInput := pending_boundary_input_prefix_unique state.toPendingBoundary stateA.toPendingBoundary
      covered (fun i before => (agrees i before).trans (agree i before).symm)
    obtain ⟨copied, slice, length, inputEq⟩ := ledger
    rw [sameInput] at inputEq
    exact ⟨copied, by simpa only [acceptedEq] using slice, length.trans acceptedEq, inputEq⟩
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, filledInput, filledOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, startF, lookF, agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    have ledgerF := fill_window_run_input_ledger boundary.toPendingBoundary short wrapD buffers inputValid
      fillRun filledState.toPendingBoundary fillAccount startF agreesF
    have coveredF : filledOrigin ≤ origin + fillEnd d := by dsimp only [fillEnd]; omega
    have endpointF : filledOrigin + fillEnd filled = origin + fillEnd d + accepted := by
      dsimp only [fillEnd]
      omega
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    by_cases wait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · have parts := wait
      simp only [Bool.and_eq_true, decide_eq_true_eq] at parts
      have flushNo : flush = Z_NO_FLUSH := beq_iff_eq.mp parts.2
      have actual : deflate_slow_body (some (.tab ds)) flush st h =
          .ok ({ st with ret := some need_more }, filledHeap) := by
        rw [slow_body_search_decision_source]
        simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
          fillRun, filledState.good.live.hs, wait, ite_true, pure_app]
      exact identify actual filledState fillAccount agreesF endpointF coveredF ledgerF
    · have notWait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := Bool.eq_false_iff.mpr wait
      by_cases empty : filled.lookahead = 0
      · have notWaitZero : (decide ((0 : UInt32) < MIN_LOOKAHEAD_u) && flush == Z_NO_FLUSH) = false := by
          simpa only [empty] using notWait
        have actual : deflate_slow_body (some (.tab ds)) flush st h =
            .ok ({ st with brk := true }, filledHeap) := by
          rw [slow_body_search_decision_source]
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false,
            empty, notWaitZero, BEq.rfl, ite_true, pure_app]
        exact identify actual filledState fillAccount agreesF endpointF coveredF ledgerF
      · have nonzero : 1 ≤ filled.lookahead.toNat := by
          have value : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
        obtain ⟨delivered, expected, other, otherZ, otherD, otherBase, otherYs, suffix, otherState,
            _endA, _buffersA, accountA, _progress, _less, endA, _baseA, _brkA, _retA, _reasonA, _readyA, _contA⟩ :=
          slow_search_decision_ready_boundary filledState filledEnd filledBuffers nonzero (fun _ => roomF)
            positive pointerF memory (publish.fill frameF) flush st
        have actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (expected, other) := by
          rw [slow_body_search_decision_source]
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false,
            beq_eq_false_iff_ne.mpr empty]
          exact suffix
        exact identify actual otherState (stream_accounting_trans fillAccount accountA) agreesF
          (by simpa only [endA, Nat.add_zero] using endpointF) coveredF
          (by simpa only [endA, Nat.add_zero] using ledgerF)
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, otherZ, otherD, otherBase, otherYs, suffix, otherState,
        _endA, _buffersA, accountA, _progress, _less, endA, _baseA, _brkA, _retA, _reasonA, _readyA, _contA⟩ :=
      slow_search_decision_ready_boundary boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish flush st
    have actual := (slow_ready_body_source boundary.good.live.hs ready flush st).trans suffix
    exact identify actual otherState accountA (fun _ _ => rfl) (by rw [endA, Nat.add_zero])
      (by dsimp only [fillEnd]; omega)
      ⟨[], caller_input_zero_slice boundary.good buffers, rfl, by rw [endA, List.append_nil]⟩

end Zlib.Deflate.Engine.Proofs
