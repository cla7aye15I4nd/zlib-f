import ZlibF.Proof.«deflate.c.engine.finish-prefix-size»
import ZlibF.Proof.«deflate.c.engine.public-finish-phase»

/-! # Actual prepared FINISH dispatch retains its two size phases -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Metadata of a returned prepared FINISH execution. Working paths retain
an exact counted prefix. Finishing paths owe at most one four-byte trailer
in addition to their one final-block overhead. The theorem below derives
this predicate on the same actual returned heap. -/
def PreparedFinishSizeResult (after : Heap) (r : ZStreamRef) (ds : Nat)
    (z' : ZStream) (result : DeflateState) (config : EngineConfig)
    (before : DeflateState) (origin base used produced : Nat) : Prop :=
  (∃ input' origin' base' ys blocks,
    BufferedBoundary after r ds z' result input' origin' base' ys config ∧ result.status = BUSY_STATE ∧
    origin' + fillEnd result = origin + fillEnd before + used ∧ base ≤ base' ∧
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
    (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
    16383 * blocks ≤ base' - base ∧
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      (before.bi_valid.toInt.toNat + 7) / 8 + (base' - base) + 5 * blocks) ∨
  (FinishingPhase result config ∧ z'.avail_in = 0 ∧ ∃ blocks delta finalBytes,
    16383 * blocks ≤ delta ∧ delta + finalBytes ≤ origin + fillEnd before + used - base ∧
    produced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) ≤
      (before.bi_valid.toInt.toNat + 7) / 8 + delta + finalBytes + 5 * blocks + 9)

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (prepared BUSY FINISH).
The actual need_more path keeps its working prefix cost. A started final
block retains four owed trailer bytes; a completed final block executes
the actual trailer and conserves those four bytes through publication.
No final overhead is charged to the working branch. This is a prepared
data-suffix result; entry pending drain, init and public histories are
separate compositions. -/
theorem public_busy_slow_finish_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d) (window : config.windowBits = 15)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PreparedFinishSizeResult after r ds z' result config d origin base used produced ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishing, classification⟩ :=
    deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  have strategyConfig : config.strategy = Z_DEFAULT_STRATEGY :=
    (congrArg EngineConfig.strategy boundary.configuration).symm.trans strategy
  have finishingBudget : ret ≠ need_more → ∃ blocks delta finalBytes,
      16383 * blocks ≤ delta ∧ delta + finalBytes ≤ origin + fillEnd d + used - base ∧
      produced + middleD.pending.toNat + (middleD.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + delta + finalBytes + 5 * blocks + 5 := by
    intro nonterminal
    obtain ⟨blocks, delta, finalBytes, closed, minimum, mass, cost, early, _final⟩ :=
      deflate_slow_finish_run_counted_size (boundary.strategy publish) boundary.end_frontier buffers positive pointer
        memory wrap window strategyConfig publish inputValid candidate floor quality strategyRun
        stateM.good.live.hs stateM.good.live.hz accountM
    cases closedEq : closed with
    | false => exact False.elim (nonterminal (early closedEq).2)
    | true =>
      rw [closedEq] at cost
      exact ⟨blocks, delta, finalBytes, minimum, mass, cost⟩
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    obtain ⟨inputP, originP, baseP, symbolsP, blocksP, stateP, endP, _buffersP,
        endpointP, baseLeP, candidateP, floorP, qualityP, minimumP, costP⟩ :=
      deflate_slow_finish_need_more_run_counted_size (boundary.strategy publish) boundary.end_frontier buffers
        positive pointer memory wrap window strategyConfig publish inputValid candidate floor quality strategyRun
        stateM.good.live.hs stateM.good.live.hz accountM
    have stateF := last_flush_buffered_boundary (stateP.buffered endP controlsM.empty_cursor) (-1)
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers stateM.good buffersM (-1), accountM, Or.inl rfl, stateF.bits,
      Or.inl ⟨inputP, originP, baseP, symbolsP, blocksP, stateF, controlsM.status.trans status,
        endpointP, baseLeP, candidateP, floorP, qualityP, minimumP, costP⟩, Or.inl rfl, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    obtain ⟨blocksF, deltaF, finalBytesF, minimumF, massF, costF⟩ := finishingBudget (by decide +kernel)
    have finished := finishing (by decide)
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have stateS := buffered_finish_status stateM
    have stateF := last_flush_buffered_boundary stateS (-1)
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    have phase := finishing_phase_of_buffered stateF rfl finished.1 finished.2 wrapM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers goodS buffersS (-1), accountM, Or.inl rfl, stateF.bits, Or.inr ⟨phase, _empty, blocksF, deltaF, finalBytesF, minimumF, massF, ?_⟩, Or.inl rfl, ?_⟩
    · change produced + middleD.pending.toNat + (if middleD.wrap = 1 then 4 else 0) ≤ _
      rw [if_pos wrapM]
      omega
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    obtain ⟨blocksF, deltaF, finalBytesF, minimumF, massF, costF⟩ := finishingBudget (by decide +kernel)
    have finished := finishing (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    obtain ⟨trailerProduced, after, z', result, _written, _pendingBits, trailerRun, goodA, buffersA, accountA,
      _sizes, _storage, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _trailerBits⟩ :=
      zlib_trailer_publish goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have phase : FinishingPhase result config := by
      refine ⟨by rw [fields], by rw [fields]; exact finished.1, bitsA, ?_, Or.inr wrapA, ?_⟩
      · rw [wrapA, fields]
        change { engineConfig middleD with wrap := -1 } = { config with wrap := -1 }
        rw [stateM.configuration]
      · intro positiveWrap
        rw [wrapA] at positiveWrap
        cases (show (-1 : Int32) ≠ 1 from by decide) positiveWrap
    have inputA : z'.avail_in = 0 := UInt32.toNat_inj.mp (by
      change z'.avail_in.toNat = 0
      have count := accountA.2.2.1
      rw [empty] at count
      change z'.avail_in.toNat + 0 = 0 at count
      omega)
    have owedCost : produced + trailerProduced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + deltaF + finalBytesF + 5 * blocksF + 9 := by
      have negative : result.wrap ≠ 1 := by rw [wrapA]; decide +kernel
      rw [if_neg negative]
      omega
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, Or.inr ⟨phase, inputA, blocksF, deltaF, finalBytesF, minimumF, massF, owedCost⟩, ?_, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · by_cases queued : result.pending = 0 <;> simp [queued]
    · rw [bitsA]
      decide
    · right
      rw [fields]
      exact controlsM.last_flush
    · intro ended
      have drained : result.pending = 0 := by
        by_cases queued : result.pending = 0
        · exact queued
        · simp [queued, show Z_OK ≠ Z_STREAM_END from by decide] at ended
      have inputA : z'.avail_in = 0 := by
        have count := accountA.2.2.1
        rw [empty] at count
        apply UInt32.toNat_inj.mp
        change z'.avail_in.toNat = 0
        change z'.avail_in.toNat + 0 = 0 at count
        omega
      exact ⟨phase.status, wrapA, inputA, phase.lookahead, drained, bitsA⟩

end Zlib.Deflate.Engine.Proofs
