import ZlibF.Proof.«deflate.c.engine.decision-counted-size»
import ZlibF.Proof.«deflate.c.engine.body-size-history»
import ZlibF.Proof.«deflate.c.engine.search-ready-step»

/-! # Actual search and refill compose one counted block-cost step -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem boundary_base_unique {h : Heap} {r : ZStreamRef} {ds origin a b : Nat}
    {z : ZStream} {d : DeflateState} {input otherInput : Nat → UInt8} {xs ys : List Symbol}
    (left : ContentBoundary h r ds z d input origin a xs)
    (right : ContentBoundary h r ds z d otherInput origin b ys) : a = b := by
  have symbols := symbol_boundary_symbols_unique left.symbols right.symbols
  have first := left.accounted
  have second := right.accounted
  rw [symbols] at first
  omega

/-- Actual insertion/search changes no output bits. Its saved match
fields supply the real decision's quality premise, so the zero/one-block
cost result composes through this complete actual suffix. -/
theorem slow_search_decision_run_counted_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base base' produced : Nat} {z z' : ZStream} {d result : DeflateState}
    {input otherInput : Nat → UInt8} {xs ys : List Symbol} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (returned : ContentBoundary after r ds z' result otherInput origin base' ys)
    (account : StreamAccounting z z' 0 produced) :
    ∃ k, k ≤ 1 ∧ 16383 * k ≤ base' - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (base' - base) + 5 * k := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, frame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  obtain ⟨_fresh, previous, sourceFloor⟩ := slow_search_run_size_facts boundary.toContentBoundary room
    candidate floor searchRun cut.good.live.hs
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame; rw [frame]
  have configuration : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configuration
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configuration
  have strategyS : searched.strategy = config.strategy := congrArg EngineConfig.strategy configuration
  have ready := publish.slow slowFrame
  obtain ⟨decision⟩ := slow_decision_all_search_boundary cut searchedBuffers (by rw [frame]; exact lookahead)
    (by rw [frame]; exact boundary.strict) (by rw [levelS]; exact positive) pointer ready.2.1
    (by rw [memoryS]; exact memory) ready.1 (by have := ready.2.2; omega) (boundary.clear.slow slowFrame) flush st head
  obtain ⟨k, count, minimum, cost⟩ := slow_decision_run_counted_size cut searchedBuffers
    (by rw [frame]; exact lookahead) (by rw [frame]; exact boundary.strict) (by rw [levelS]; exact positive)
    pointer ready.2.1 (by rw [memoryS]; exact memory) ready.1 (by have := ready.2.2; omega)
    (boundary.clear.slow slowFrame) (by rw [strategyS]; exact strategy) previous sourceFloor quality decision
  unfold slowSearchDecision at observed
  rw [bind_app, searchRun] at observed
  have pairs := Prod.mk.inj (Except.ok.inj (decision.run.symm.trans observed))
  have boundaryA := decision.boundary
  rw [pairs.2] at boundaryA
  have streams : decision.stream = z' := Option.some.inj (boundaryA.good.live.hz.symm.trans returned.good.live.hz)
  have states : decision.state = result := Option.some.inj (boundaryA.good.live.hs.symm.trans returned.good.live.hs)
  rw [streams, states] at boundaryA
  have bases : decision.blockBase = base' := boundary_base_unique boundaryA returned
  have accountA := decision.accounting
  rw [streams] at accountA
  have amounts : decision.produced = produced := by
    have first := accountA.2.2.2.1
    have second := account.2.2.2.1
    omega
  have bitsS : searched.bi_valid = d.bi_valid := by rw [frame]
  exact ⟨k, count, by rwa [bases] at minimum, by rwa [amounts, states, bitsS, bases] at cost⟩

private theorem transfer_body_count {middle after : Heap} {r : ZStreamRef}
    {ds origin knownOrigin finalOrigin base knownBase finalBase used knownUsed produced knownProduced k : Nat}
    {z knownZ finalZ : ZStream} {d knownD finalD : DeflateState}
    {knownInput finalInput : Nat → UInt8} {knownSymbols finalSymbols : List Symbol}
    (heaps : middle = after)
    (known : ContentBoundary middle r ds knownZ knownD knownInput knownOrigin knownBase knownSymbols)
    (returned : ContentBoundary after r ds finalZ finalD finalInput finalOrigin finalBase finalSymbols)
    (accountK : StreamAccounting z knownZ knownUsed knownProduced)
    (accountA : StreamAccounting z finalZ used produced)
    (endpointK : knownOrigin + fillEnd knownD = origin + fillEnd d + knownUsed)
    (endpointA : finalOrigin + fillEnd finalD = origin + fillEnd d + used)
    (count : k ≤ 1) (minimum : 16383 * k ≤ knownBase - base)
    (cost : knownProduced + knownD.pending.toNat + (knownD.bi_valid.toInt.toNat + 7) / 8 ≤
      (d.bi_valid.toInt.toNat + 7) / 8 + (knownBase - base) + 5 * k) :
    ∃ blocks, blocks ≤ 1 ∧ 16383 * blocks ≤ finalBase - base ∧
      produced + finalD.pending.toNat + (finalD.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (finalBase - base) + 5 * blocks := by
  rw [heaps] at known
  have streams : knownZ = finalZ := Option.some.inj (known.good.live.hz.symm.trans returned.good.live.hz)
  have states : knownD = finalD := Option.some.inj (known.good.live.hs.symm.trans returned.good.live.hs)
  rw [streams] at accountK
  have usedEq : knownUsed = used := by
    have first := accountK.2.2.1
    have second := accountA.2.2.1
    omega
  have producedEq : knownProduced = produced := by
    have first := accountK.2.2.2.1
    have second := accountA.2.2.2.1
    omega
  have origins : knownOrigin = finalOrigin := by rw [states, usedEq] at endpointK; omega
  rw [streams, states, origins] at known
  have bases : knownBase = finalBase := boundary_base_unique known returned
  exact ⟨k, count, by rwa [bases] at minimum, by rwa [producedEq, states, bases] at cost⟩

/-- A complete actual body, including refill/sliding and both early
stops, adds zero or one full block. The exact accepted-input endpoint
identifies the same logical origin even after a slide. -/
theorem slow_body_run_counted_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin finalOrigin base finalBase used produced : Nat} {z z' : ZStream} {d result : DeflateState}
    {input otherInput : Nat → UInt8} {xs ys : List Symbol} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY) (window : d.w_size.toNat = 32768)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (returned : ContentBoundary after r ds z' result otherInput finalOrigin finalBase ys)
    (account : StreamAccounting z z' used produced)
    (endpoint : finalOrigin + fillEnd result = origin + fillEnd d + used) :
    ∃ k, k ≤ 1 ∧ 16383 * k ≤ finalBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (finalBase - base) + 5 * k := by
  have suffix {middle : Heap} {entryZ : ZStream} {entryD : DeflateState}
      {entryInput : Nat → UInt8} {entryOrigin entryUsed : Nat}
      (state : StrategyBoundary middle r ds entryZ entryD entryInput entryOrigin base xs config)
      (endS : EndFrontier middle entryD) (buffersS : StreamBuffers middle r)
      (pointerS : entryZ.next_out = .ref (.blk ob) oo) (readyS : PublishReady entryD)
      (candidateS : ShortCandidateQuality entryD) (floorS : StoredSourceFloor entryD)
      (accountS : StreamAccounting z entryZ entryUsed 0)
      (endpointS : entryOrigin + fillEnd entryD = origin + fillEnd d + entryUsed)
      (bitsS : entryD.bi_valid = d.bi_valid)
      (look : 1 ≤ entryD.lookahead.toNat)
      (room : 3 ≤ entryD.lookahead.toNat → entryD.strstart.toNat + 262 ≤ entryD.window_size.toNat)
      (actual : slowSearchDecision (some (.tab ds)) flush st middle = .ok (next, after)) :
      ∃ k, k ≤ 1 ∧ 16383 * k ≤ finalBase - base ∧
        produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
          (d.bi_valid.toInt.toNat + 7) / 8 + (finalBase - base) + 5 * k := by
    obtain ⟨amount, answer, computed, nextZ, nextD, nextBase, nextSymbols, run, stateA, _endA, _buffersA,
      accountA, _startA, _lookA, endpointA, _baseA, _brk, _returns, _reason, _continues⟩ :=
      slow_search_decision_ready_boundary state endS buffersS look room positive pointerS memory readyS flush st
    obtain ⟨k, count, minimum, cost⟩ := slow_search_decision_run_counted_size state endS buffersS look room
      positive pointerS memory strategy readyS candidateS floorS quality run stateA.toContentBoundary accountA
    have total : StreamAccounting z nextZ entryUsed amount := by
      simpa only [Nat.add_zero, Nat.zero_add] using stream_accounting_trans accountS accountA
    have endpointA' : entryOrigin + fillEnd nextD = origin + fillEnd d + entryUsed := by rw [endpointA]; exact endpointS
    rw [bitsS] at cost
    exact transfer_body_count (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2 stateA.toContentBoundary returned
      total account endpointA' endpoint count minimum cost
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨read, filledHeap, filledZ, filled, extended, nextOrigin, _before, fillRun,
      filledState, filledFrontier, fillAccount, filledBuffers, fillStart, fillLook, _agrees,
      _stopped, frameF, ready, _pendingBefore, _bytes, _pendingAfter, _prefixes⟩ :=
      fill_window_strategy_encoding boundary frontier short wrap buffers inputValid pointer publish
    have actualWrap : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨candidateF, floorF⟩ := fill_window_run_size_facts boundary.toContentBoundary.toPendingBoundary
      short actualWrap buffers inputValid window candidate floor fillRun filledState.good.live.hs
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
      rw [fillAccount.2.2.2.2.2.1, advance_zero]; exact pointer
    have roomF := fill_window_run_comparison_room boundary.toContentBoundary.toPendingBoundary short actualWrap
      buffers inputValid fillRun filledState.good.live.hs
    have endpointF : nextOrigin + fillEnd filled = origin + fillEnd d + read := by dsimp only [fillEnd]; omega
    have bitsF : filled.bi_valid = d.bi_valid := by rw [frameF]
    have stoppedCost (heaps : filledHeap = after) :
        ∃ k, k ≤ 1 ∧ 16383 * k ≤ finalBase - base ∧
          produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
            (d.bi_valid.toInt.toNat + 7) / 8 + (finalBase - base) + 5 * k := by
      apply transfer_body_count heaps filledState.toContentBoundary returned fillAccount account endpointF endpoint
        (k := 0) (by decide)
      · simp
      · rw [ready.1, UInt64.toNat_zero, bitsF]; simp
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    rw [slow_body_search_decision_source] at observed
    simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true, fillRun,
      filledState.good.live.hs] at observed
    by_cases waiting : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · simp only [waiting, ite_true, pure_app] at observed
      exact stoppedCost (Prod.mk.inj (Except.ok.inj observed)).2
    · have notWaiting : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := Bool.eq_false_iff.mpr waiting
      simp only [notWaiting, Bool.false_eq_true, ite_false] at observed
      by_cases empty : filled.lookahead = 0
      · simp only [empty, beq_self_eq_true, ite_true, pure_app] at observed
        exact stoppedCost (Prod.mk.inj (Except.ok.inj observed)).2
      · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at observed
        have look : 1 ≤ filled.lookahead.toNat := by
          have ne : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        exact suffix filledState filledFrontier filledBuffers pointerF ready candidateF floorF fillAccount endpointF bitsF
          look (fun _ => roomF) observed
  · have notSmall : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
      rw [UInt32.lt_iff_toNat_lt]; exact short
    rw [slow_body_search_decision_source] at observed
    simp only [bind_app, rdD_eq, boundary.good.live.hs, notSmall, ite_false] at observed
    have range := boundary.range
    dsimp only [fillEnd] at range
    exact suffix boundary frontier buffers pointer publish candidate floor (stream_accounting_zero z) (by simp) rfl
      (by omega) (fun _ => by omega) observed

end Zlib.Deflate.Engine.Proofs
