import ZlibF.Proof.«deflate.c.engine.search-decision-prefix»
import ZlibF.Proof.«deflate.c.engine.refill-encoding»
import ZlibF.Proof.«deflate.c.engine.finish-strategy-step»

/-! # The complete actual slow body retains its independent encoding alternative -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual slow body retains a composable encoding prefix
through refill, sliding, all stop guards, real search and every decision.
Previously accepted input prefixes stay equal across window slides. The
next absolute bit-position residue is proved for actual published blocks,
including stored blocks. All signed flush scalars and zero/short output
are admitted at the explicit initialized publishing phase. -/
theorem slow_body_strategy_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (flush : Int32) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin before written remaining,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧ written.length = produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = none → next.brk = false → result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (next.brk = true → st.brk = true ∨ (result.lookahead = 0 ∧ z'.avail_in = 0)) ∧
      (next.ret = some need_more → st.ret = some need_more ∨
        ((flush = Z_NO_FLUSH ∧ result.lookahead.toNat < 262 ∧ z'.avail_in = 0) ∨ z'.avail_out = 0)) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ((base' = base ∧ produced = 0 ∧ written = [] ∧ remaining = before) ∨
       (ys = [] ∧ ∃ blockBits, ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
          BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix extended base') ∧
          (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8)) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, before, fillRun,
      filledState, filledFrontier, fillAccount, filledBuffers, startF, lookF, agreesF,
      stoppedF, frameF, readyF, pendingBefore, bytesF, pendingF, prefixesF⟩ :=
      fill_window_strategy_encoding boundary frontier short wrap buffers inputValid pointer publish
    have pointerEq : filledZ.next_out = z.next_out := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := pointerEq.trans pointer
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + used := by
      dsimp only [fillEnd]
      omega
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    by_cases wait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · have parts := wait
      simp only [Bool.and_eq_true, decide_eq_true_eq] at parts
      have shortF : filled.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp parts.1
      have flushNo : flush = Z_NO_FLUSH := beq_iff_eq.mp parts.2
      have inputEmpty : filledZ.avail_in = 0 := stoppedF.resolve_left (by omega)
      refine ⟨used, 0, { st with ret := some need_more }, filledHeap, filledZ, filled, base, xs,
        extended, nextOrigin, before, [], before, ?_, filledState, filledFrontier,
        filledBuffers, fillAccount, rfl, agreesF, endpointF, Nat.le_refl _, Or.inr rfl,
        ?_, ?_, ?_, ?_, pendingBefore, bytesF, pendingF, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · rw [slow_body_search_decision_source]
        simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
          fillRun, filledState.good.live.hs, wait, ite_true, pure_app]
      · intro _ impossible; cases impossible
      · intro impossible; cases impossible
      · intro broke; exact Or.inl broke
      · intro _; exact Or.inr (Or.inl ⟨flushNo, shortF, inputEmpty⟩)
    · have notWait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := Bool.eq_false_iff.mpr wait
      by_cases empty : filled.lookahead = 0
      · have inputEmpty : filledZ.avail_in = 0 := stoppedF.resolve_left (by rw [empty]; change ¬ 262 ≤ 0; omega)
        refine ⟨used, 0, { st with brk := true }, filledHeap, filledZ, filled, base, xs,
          extended, nextOrigin, before, [], before, ?_, filledState, filledFrontier,
          filledBuffers, fillAccount, rfl, agreesF, endpointF, Nat.le_refl _, Or.inl rfl,
          ?_, ?_, fun _ => Or.inr ⟨empty, inputEmpty⟩, fun returned => Or.inl returned,
          pendingBefore, bytesF, pendingF, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
        · rw [slow_body_search_decision_source]
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false]
          simp only [empty, beq_self_eq_true, ite_true, pure_app]
        · intro output _; have count := fillAccount.2.2.2.1; omega
        · intro _ impossible; cases impossible
      · have nonzero : 1 ≤ filled.lookahead.toNat := by
          have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        have actualWrap : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
        have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short actualWrap buffers inputValid fillRun filledState.good.live.hs
        obtain ⟨produced, next, after, z', result, base', ys, beforeS, written, remaining,
          suffixRun, stateA, endA, buffersA, suffixAccount, length, _progress, less,
          endpoint, baseLe, brkA, returnsA, reasonA, continuesA, pendingS, bytesA, pendingA, casesA⟩ :=
          slow_search_decision_strategy_prefix (offset := offset) filledState filledFrontier filledBuffers nonzero
            (fun _ => roomF) positive pointerF memory readyF (by rw [frameF]; exact position) flush st
        have beforeEq : beforeS = before :=
          (pending_bits_zero_value readyF.1 pendingS).trans (pending_bits_zero_value readyF.1 pendingF).symm
        rw [beforeEq] at casesA
        rw [pointerEq] at bytesA
        have accountA : StreamAccounting z z' used produced := by
          simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans fillAccount suffixAccount
        refine ⟨used, produced, next, after, z', result, base', ys, extended, nextOrigin,
          before, written, remaining, ?_, stateA, endA, buffersA, accountA, length,
          agreesF, ?_, baseLe, returnsA, ?_, ?_, ?_, ?_, pendingBefore, bytesA, pendingA, ?_⟩
        · rw [slow_body_search_decision_source]
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false,
            beq_eq_false_iff_ne.mpr empty]
          exact suffixRun
        · rw [endpoint]; exact endpointF
        · intro output running
          apply continuesA (by have count := fillAccount.2.2.2.1; omega) running
        · intro _ _
          have beforeCount := fillAccount.2.2.1
          have afterCount := suffixAccount.2.2.1
          omega
        · intro broke; exact Or.inl (brkA.symm.trans broke)
        · intro returned
          rcases reasonA returned with old | outputEmpty
          · exact Or.inl old
          · exact Or.inr (Or.inr outputEmpty)
        · rcases casesA with noBlock | ⟨symbols, _flag, blockBits, wire, prefixA, nextPosition⟩
          · exact Or.inl ⟨noBlock.1, noBlock.2.1, noBlock.2.2.1, noBlock.2.2.2.1⟩
          · refine Or.inr ⟨symbols, blockBits, wire, ?_, nextPosition⟩
            have baseBound : base ≤ origin + fillEnd d := by
              have accounted := boundary.accounted
              dsimp only [fillEnd]
              omega
            have historyEq := prefixesF base baseBound
            rw [← historyEq]
            exact prefixA
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have bound := boundary.range
      dsimp only [fillEnd] at bound
      omega
    obtain ⟨produced, next, after, z', result, base', ys, before, written, remaining,
      suffixRun, stateA, endA, buffersA, accountA, length, _progress, less,
      endpoint, baseLe, brkA, returnsA, reasonA, continuesA, pendingBefore, bytesA, pendingA, casesA⟩ :=
      slow_search_decision_strategy_prefix (offset := offset) boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish position flush st
    refine ⟨0, produced, next, after, z', result, base', ys, input, origin, before, written, remaining,
      ?_, stateA, endA, buffersA, accountA, length, fun _ _ => rfl, ?_, baseLe,
      returnsA, continuesA, ?_, ?_, ?_, pendingBefore, bytesA, pendingA, ?_⟩
    · have large : ¬ d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt]; exact short
      rw [slow_body_search_decision_source]
      simp only [bind_app, rdD_eq, boundary.good.live.hs, large, ite_false]
      exact suffixRun
    · rw [endpoint, Nat.add_zero]
    · intro _ _; have count := accountA.2.2.1; omega
    · intro broke; exact Or.inl (brkA.symm.trans broke)
    · intro returned
      rcases reasonA returned with old | outputEmpty
      · exact Or.inl old
      · exact Or.inr (Or.inr outputEmpty)
    · rcases casesA with noBlock | ⟨symbols, _flag, blockBits, wire, prefixA, nextPosition⟩
      · exact Or.inl ⟨noBlock.1, noBlock.2.1, noBlock.2.2.1, noBlock.2.2.2.1⟩
      · exact Or.inr ⟨symbols, blockBits, wire, prefixA, nextPosition⟩

end Zlib.Deflate.Engine.Proofs
