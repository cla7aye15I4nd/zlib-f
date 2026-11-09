import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-trailer»
import ZlibF.Proof.«deflate.c.engine.public-finish-phase»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Accepted default data dispatch preserves a working or finishing phase.
Output is a legal foreign-depth caller range. The full entry and complete
output/history/frame refinement remain separate obligations. -/
theorem public_foreign_busy_finish_data_interval_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishing, classification⟩ :=
    default_foreign_deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  have frameM := default_foreign_deflate_slow_finish_run_buffer_frame (boundary.strategy publish) boundary.end_frontier buffers
    positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
  have intervalM : ByteOutputInterval h middle (.dstate_depth owner) oo produced := by
    rw [pointer] at frameM
    exact ByteOutputInterval.of_buffer_frame frameM
  have privateInterval : ∀ result : DeflateState, result.depth = middleD.depth →
      ByteOutputInterval h (setD middle ds result) (.dstate_depth owner) oo produced := by
    intro result depth before get
    obtain ⟨array,getA,size,same⟩ := intervalM before get
    exact ⟨array,(byte_view_setD_depth stateM.good.live.hs depth _).trans getA,size,same⟩
  have privateTwice : ∀ first second : DeflateState, first.depth=middleD.depth → second.depth=first.depth →
      ByteOutputInterval h (setD (setD middle ds first) ds second) (.dstate_depth owner) oo produced := by
    intro first second firstDepth secondDepth before get
    obtain ⟨array,getA,size,same⟩ := privateInterval first firstDepth before get
    have live : (setD middle ds first).dstates ds=some first := by simp [setD]
    exact ⟨array,(byte_view_setD_depth live secondDepth _).trans getA,size,same⟩
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    have stateF := last_flush_buffered_boundary stateM (-1)
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers stateM.good buffersM (-1), accountM, privateInterval {middleD with last_flush := -1} rfl, Or.inl rfl, stateF.bits,
      Or.inl ⟨extended, nextOrigin, middleBase, ys, stateF, controlsM.status.trans status⟩, Or.inl rfl, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    have finished := finishing (by decide)
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have stateS := buffered_finish_status stateM
    have stateF := last_flush_buffered_boundary stateS (-1)
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    have phase := finishing_phase_of_buffered stateF rfl finished.1 finished.2 wrapM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers goodS buffersS (-1), accountM, privateTwice {middleD with status := FINISH_STATE} {middleD with status := FINISH_STATE,last_flush := -1} rfl rfl, Or.inl rfl, stateF.bits, Or.inr phase, Or.inl rfl, ?_⟩
    intro impossible
    cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · subst ret
    have finished := finishing (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    obtain ⟨trailerProduced, after, z', result, _written, _pendingBits, trailerRun, goodA, buffersA, accountA,
      _sizes, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _trailerBits,
      _adlerA, _inputA, _outputA, _allocA, _nextA, preciseA, _tailA⟩ :=
      foreign_zlib_trailer_publish_encoding goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have phase : FinishingPhase result config := by
      refine ⟨by rw [fields], by rw [fields]; exact finished.1, bitsA, ?_, Or.inr wrapA, ?_⟩
      · rw [wrapA, fields]
        change { engineConfig middleD with wrap := -1 } = { config with wrap := -1 }
        rw [stateM.configuration]
      · intro positiveWrap
        rw [wrapA] at positiveWrap
        cases (show (-1 : Int32) ≠ 1 from by decide) positiveWrap
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, ?_, Or.inr phase, ?_, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · have intervalT : ByteOutputInterval (setD middle ds {middleD with status := FINISH_STATE}) after (.dstate_depth owner) (oo+produced) trailerProduced := by
        rw [pointerM] at preciseA
        exact ByteOutputInterval.of_buffer_frame preciseA
      exact (privateInterval {middleD with status := FINISH_STATE} rfl).trans intervalT
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


theorem public_foreign_busy_finish_data_run_output_interval {h after : Heap} {r : ZStreamRef} {ds owner oo origin base used produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : publicDataTail (some r) (some (.tab ds)) Z_FINISH h=.ok (rc,after))
    (live : r.get after=some returned) (account : StreamAccounting z returned used produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨_used,amount,_rc,other,nextZ,_nextD,actual,goodA,_buffersA,accountA,effect,_rest⟩ :=
    public_foreign_busy_finish_data_interval_execution boundary buffers status level strategy pointer memory wrap publish inputValid
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at goodA effect
  have streams : nextZ=returned := Option.some.inj (goodA.live.hz.symm.trans live)
  rw [streams] at accountA
  have amounts : amount=produced := (stream_accounting_counts_unique accountA account).2
  exact amounts ▸ effect

end Zlib.Deflate.Engine.Proofs
