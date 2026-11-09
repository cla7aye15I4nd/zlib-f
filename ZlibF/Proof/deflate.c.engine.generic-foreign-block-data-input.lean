import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-raw-input»
import ZlibF.Proof.«deflate.c.engine.public-block-data-encoding»

/-! # Actual BLOCK data dispatch retains cumulative raw encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual BUSY BLOCK data path retains exact output,
RawPrefix and Adler for the consumed original input. The block-done
return adds no marker and includes the real exhausted-output retry store.
All strategy-entry output capacities are admitted; entry/header/pending
guards are composed separately. -/
theorem public_foreign_busy_block_data_raw_prefix_input_interval {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin nextBase ys written,
      publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      RawPrefix after result extended nextBase (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      ByteOutputInterval h after (.dstate_depth owner) oo written.length := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, ret, middle, zm, dm, extended, nextOrigin, middleBase, ys, written,
      strategyRun, stateM, endM, buffersM, accountM, bytesM, agreesM, endpointM, baseM,
      encodingM, checksumM, inputLedgerM, classification,_shapeM,frameM,controls,doneReady⟩ :=
    default_foreign_deflate_slow_nonfinal_ready_raw_prefix_input boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_BLOCK (by decide) (by decide) snapshot checksum encoding
  have strategyEffect : ByteOutputInterval h middle (.dstate_depth owner) oo written.length := by
    rw [pointer] at frameM
    exact ByteOutputInterval.of_buffer_frame frameM
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_BLOCK h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_BLOCK (by decide)]
    simp only [bind_app, strategyRun]
  have statusM : dm.status = BUSY_STATE := controls.status.trans status
  have bufferedM := stateM.buffered endM controls.empty_cursor
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _inputEmpty, _lookEmpty, _symbols⟩
  · subst ret
    have returned := public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_BLOCK
    have bytesF := caller_bytes_setD_depth (result := {dm with last_flush := -1}) stateM.good.live.hs rfl bytesM
    have finalEffect : ByteOutputInterval middle (setD middle ds {dm with last_flush:= -1}) (.dstate_depth owner) (oo+written.length) 0 := .of_same (byte_view_setD_depth (result:={dm with last_flush:= -1}) stateM.good.live.hs rfl _)
    exact ⟨used, _, zm, _, extended, nextOrigin, middleBase, ys, written,
      sourceRun.trans returned, last_flush_buffered_boundary bufferedM (-1),
      last_flush_buffers stateM.good buffersM (-1), accountM, bytesF, agreesM, endpointM, baseM,
      statusM, Or.inr rfl, encodingM.last_flush stateM.good (-1), checksumM, inputLedgerM,by simpa only [Nat.add_zero] using strategyEffect.trans finalEffect⟩
  · subst ret
    have readyM := (doneReady rfl).1
    have returned := public_strategy_block_done_ready stateM.good readyM
    by_cases exhausted : (zm.avail_out == 0) = true
    · have bytesF := caller_bytes_setD_depth (result := {dm with last_flush := -1}) stateM.good.live.hs rfl bytesM
      have finalEffect : ByteOutputInterval middle (setD middle ds {dm with last_flush:= -1}) (.dstate_depth owner) (oo+written.length) 0 := .of_same (byte_view_setD_depth (result:={dm with last_flush:= -1}) stateM.good.live.hs rfl _)
      exact ⟨used, _, zm, _, extended, nextOrigin, middleBase, ys, written,
        sourceRun.trans (by simpa only [exhausted, ite_true] using returned),
        last_flush_buffered_boundary bufferedM (-1), last_flush_buffers stateM.good buffersM (-1), accountM, bytesF,
        agreesM, endpointM, baseM, statusM, Or.inr rfl, encodingM.last_flush stateM.good (-1), checksumM, inputLedgerM,by simpa only [Nat.add_zero] using strategyEffect.trans finalEffect⟩
    · exact ⟨used, middle, zm, dm, extended, nextOrigin, middleBase, ys, written,
        sourceRun.trans (by simpa only [exhausted, Bool.false_eq_true, ite_false] using returned),
        bufferedM, buffersM, accountM, bytesM, agreesM, endpointM, baseM, statusM, Or.inl controls.last_flush,
        encodingM, checksumM, inputLedgerM,strategyEffect⟩

/-- The complete actual BUSY BLOCK data path retains exact output,
RawPrefix and Adler for the consumed original input. The block-done
return adds no marker and includes the real exhausted-output retry store.
All strategy-entry output capacities are admitted; entry/header/pending
guards are composed separately. -/
theorem public_foreign_busy_block_data_raw_prefix_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin nextBase ys written,
      publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      RawPrefix after result extended nextBase (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  obtain ⟨used,after,z',result,extended,nextOrigin,nextBase,ys,written,
    run,stateA,buffersA,accountA,bytesA,agreesA,endpointA,baseA,statusA,lastA,encodingA,checksumA,inputLedgerA,_intervalA⟩ :=
    public_foreign_busy_block_data_raw_prefix_input_interval boundary frontier buffers status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
  exact ⟨used,after,z',result,extended,nextOrigin,nextBase,ys,written,
    run,stateA,buffersA,accountA,bytesA,agreesA,endpointA,baseA,statusA,lastA,encodingA,checksumA,inputLedgerA⟩

end Zlib.Deflate.Engine.Proofs
