import ZlibF.Proof.«deflate.c.engine.decision-search-encoding»
import ZlibF.Proof.«deflate.c.engine.short-strategy-step»

/-! # Actual search and every decision retain the same independent encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual insertion/search followed by every match/literal/defer decision
retains the initialized strategy boundary and the exact independent block
meaning. Search preserves the held-bit prefix. No candidate, branch or
encoding is selected by a premise. Caller output may be zero or short;
the explicit publishing phase is established before actual strategy entry.
Refill, the complete loop and public encoded histories remain separate. -/
theorem slow_search_decision_strategy_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (publish : PublishReady d)
    (flush : Int32) (st : LoopS) :
    ∃ produced next after z' result base' ys before written remaining,
      slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result input origin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ written.length = produced ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ base ≤ base' ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ((base' = base ∧ produced = 0 ∧ written = [] ∧ remaining = before ∧ next.bflush = false) ∨
       (ys = [] ∧ next.bflush = true ∧
        ∃ kind body, kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
          (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
          ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
            ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix (inputPrefix input base'))) := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  have slowFrame : SlowRecordFrame d searched := by
    unfold SlowRecordFrame
    rw [searchFrame]
  have configS : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configS
  have positiveS : 1 ≤ searched.lookahead.toNat := by rw [searchFrame]; exact lookahead
  have strictS : searched.sym_next.toNat < searched.sym_end.toNat := by rw [searchFrame]; exact boundary.strict
  have readyS := publish.slow slowFrame
  have clearS := boundary.clear.slow slowFrame
  obtain ⟨decision, beforeS, written, remaining, pendingS, length, bytesA, pendingA, casesA⟩ :=
    slow_decision_all_search_encoding cut searchedBuffers positiveS strictS
      (by rw [levelS]; exact positive) pointer readyS.2.1 (by rw [memoryS]; exact memory)
      readyS.1 readyS.2.2 clearS flush st head
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
  have beforeInitial := pending_bits_base trees publish.2.1
  have fromSearch := pending_bits_zero_value readyS.1 pendingS
  have fromInitial := pending_bits_zero_value publish.1 beforeInitial
  have wordS : searched.bi_buf = d.bi_buf := by rw [slowFrame]
  have validS : searched.bi_valid = d.bi_valid := by rw [slowFrame]
  rw [wordS, validS] at fromSearch
  have beforeEq : beforeS = Zlib.Trees.Proofs.Out.outBits buf d := fromSearch.trans fromInitial.symm
  rw [beforeEq] at casesA
  have configuration : engineConfig decision.state = config := Eq.trans decision.config configS
  have stateA : StrategyBoundary decision.after r ds decision.stream decision.state input origin
      decision.blockBase decision.symbols config :=
    ⟨decision.boundary, configuration, decision.clear, decision.bits, decision.strict, decision.resume⟩
  refine ⟨decision.produced, decision.next, decision.after, decision.stream, decision.state,
    decision.blockBase, decision.symbols, Zlib.Trees.Proofs.Out.outBits buf d, written, remaining,
    ?_, stateA, decision.frontier, decision.buffers, decision.accounting, length,
    ?_, ?_, ?_, decision.base_le, decision.brk, decision.returns, decision.reason,
    decision.continues, beforeInitial, bytesA, pendingA, casesA⟩
  · unfold slowSearchDecision
    rw [bind_app, searchRun]
    exact decision.run
  · have startEq : searched.strstart = d.strstart := by rw [searchFrame]
    rw [← startEq]
    exact decision.progress
  · have lookEq : searched.lookahead = d.lookahead := by rw [searchFrame]
    rw [← lookEq]
    exact decision.less
  · have endpoint : fillEnd searched = fillEnd d := by rw [searchFrame]; rfl
    exact decision.endpoint.trans endpoint

end Zlib.Deflate.Engine.Proofs
