import ZlibF.Proof.«deflate.c.engine.decision-size-preserve»
import ZlibF.Proof.«deflate.c.engine.refill-encoding»
import ZlibF.Proof.«deflate.c.engine.short-strategy-step»

/-! # A complete actual slow body retains the block-cost history facts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Actual search transfers quality to the saved fields, then every real
decision retains quality on its returned state and symbol ledger. -/
theorem slow_search_decision_run_size_facts {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs ys : List Symbol} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (publish : PublishReady d)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) (symbols : SymbolBoundary after ds result ys) :
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, frame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  obtain ⟨fresh, previous, sourceFloor⟩ := slow_search_run_size_facts boundary.toContentBoundary room
    candidate floor searchRun cut.good.live.hs
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame; rw [frame]
  have configuration : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configuration
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configuration
  have ready := publish.slow slowFrame
  unfold slowSearchDecision at observed
  rw [bind_app, searchRun] at observed
  exact slow_decision_run_size_facts cut searchedBuffers (by rw [frame]; exact lookahead)
    (by rw [frame]; exact boundary.strict) (by rw [levelS]; exact positive) pointer ready.2.1
    (by rw [memoryS]; exact memory) ready.1 (by have := ready.2.2; omega) (boundary.clear.slow slowFrame)
    fresh previous sourceFloor quality observed live symbols

/-- Refill/sliding, both early stops, actual insertion/filtering and every
decision preserve the size facts on the actual returned ledger. Every
signed flush and caller capacity are admitted at the existing initialized
publication phase. Init establishes these facts separately; a public
size bound and utility-success claim still need whole-call composition. -/
theorem slow_body_run_size_facts {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs ys : List Symbol} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : d.w_size.toNat = 32768)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) (symbols : SymbolBoundary after ds result ys) :
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, before, fillRun,
      filledState, filledFrontier, fillAccount, filledBuffers, _start, _look, _agrees,
      _stopped, _frame, ready, _pendingBefore, _bytes, _pendingAfter, _prefixes⟩ :=
      fill_window_strategy_encoding boundary frontier short wrap buffers inputValid pointer publish
    have actualWrap : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨candidateF, floorF⟩ := fill_window_run_size_facts boundary.toContentBoundary.toPendingBoundary
      short actualWrap buffers inputValid window candidate floor fillRun filledState.good.live.hs
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]
      exact pointer
    have roomF := fill_window_run_comparison_room boundary.toContentBoundary.toPendingBoundary short actualWrap
      buffers inputValid fillRun filledState.good.live.hs
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    rw [slow_body_search_decision_source] at observed
    simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true, fillRun,
      filledState.good.live.hs] at observed
    have stoppedFacts (sameHeap : filledHeap = after) :
        ShortCandidateQuality result ∧ StoredSourceFloor result ∧
          (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
      have get := filledState.good.live.hs
      have ledger := filledState.symbols
      rw [sameHeap] at get ledger
      have stateEq : filled = result := Option.some.inj (get.symm.trans live)
      rw [stateEq] at ledger candidateF floorF
      have sameSymbols : xs = ys := symbol_boundary_symbols_unique ledger symbols
      rw [sameSymbols] at quality
      exact ⟨candidateF, floorF, quality⟩
    by_cases waiting : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · simp only [waiting, ite_true, pure_app] at observed
      exact stoppedFacts (Prod.mk.inj (Except.ok.inj observed)).2
    · have notWaiting : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := Bool.eq_false_iff.mpr waiting
      simp only [notWaiting, Bool.false_eq_true, ite_false] at observed
      by_cases empty : filled.lookahead = 0
      · simp only [empty, beq_self_eq_true, ite_true, pure_app] at observed
        exact stoppedFacts (Prod.mk.inj (Except.ok.inj observed)).2
      · have nonzero : (filled.lookahead == 0) = false := beq_eq_false_iff_ne.mpr empty
        simp only [nonzero, Bool.false_eq_true, ite_false] at observed
        have positiveF : 1 ≤ filled.lookahead.toNat := by
          have notZero : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        exact slow_search_decision_run_size_facts filledState filledFrontier filledBuffers positiveF (fun _ => roomF)
          positive pointerF memory ready candidateF floorF quality observed live symbols
  · have notSmall : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
      rw [UInt32.lt_iff_toNat_lt]
      exact short
    rw [slow_body_search_decision_source] at observed
    simp only [bind_app, rdD_eq, boundary.good.live.hs, notSmall, ite_false] at observed
    have range := boundary.range
    dsimp only [fillEnd] at range
    exact slow_search_decision_run_size_facts boundary frontier buffers (by omega) (fun _ => by omega)
      positive pointer memory publish candidate floor quality observed live symbols

end Zlib.Deflate.Engine.Proofs
