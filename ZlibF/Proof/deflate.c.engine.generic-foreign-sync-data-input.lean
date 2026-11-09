import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-raw-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-return»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-return»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.public-partial-sync-data-encoding»

/-! # Complete actual SYNC data paths retain observed encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual BUSY SYNC data dispatch combines slow
compression, marker generation, pending publication and retry stores.
Exact final-heap output, raw meaning and Adler use the consumed original
caller input. Logical accepted input and both initialized frontiers stay
connected for every strategy-entry output capacity, including zero.
The surrounding public entry/header/pending guards are separate. -/
theorem public_foreign_busy_sync_data_raw_prefix_input_interval {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
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
      publicDataTail (some r) (some (.tab ds)) Z_SYNC_FLUSH h = .ok (Z_OK, after) ∧
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
  have nonzero : Z_SYNC_FLUSH ≠ Z_NO_FLUSH := by decide
  have nonfinal : Z_SYNC_FLUSH ≠ Z_FINISH := by decide
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, ret, middle, zm, dm, extended, nextOrigin, middleBase, ys, writtenS,
      strategyRun, stateM, endM, buffersM, accountM, bytesM, agreesM, endpointM, baseM,
      encodingM, checksumM, inputLedgerM, classification,_shapeM,frameM,controls,doneReady⟩ :=
    default_foreign_deflate_slow_nonfinal_ready_raw_prefix_input boundary frontier buffers positive pointer memory wrap publish inputValid
      Z_SYNC_FLUSH nonzero nonfinal snapshot checksum encoding
  have strategyEffect : ByteOutputInterval h middle (.dstate_depth owner) oo writtenS.length := by
    rw [pointer] at frameM
    exact ByteOutputInterval.of_buffer_frame frameM
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_SYNC_FLUSH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_SYNC_FLUSH ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy Z_SYNC_FLUSH nonzero]
    simp only [bind_app, strategyRun]
  have statusM : dm.status = BUSY_STATE := controls.status.trans status
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, _inputEmpty, _lookEmpty, symbols⟩
  · subst ret
    have returned := public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted Z_SYNC_FLUSH
    have bufferedM := stateM.buffered endM controls.empty_cursor
    have bytesF := caller_bytes_setD_depth (result := {dm with last_flush := -1}) stateM.good.live.hs rfl bytesM
    have finalEffect : ByteOutputInterval middle (setD middle ds {dm with last_flush := -1}) (.dstate_depth owner) (oo + writtenS.length) 0 := .of_same (byte_view_setD_depth (result:={dm with last_flush:= -1}) stateM.good.live.hs rfl _)
    exact ⟨used, _, zm, _, extended, nextOrigin, middleBase, ys, writtenS,
      sourceRun.trans returned, last_flush_buffered_boundary bufferedM (-1),
      last_flush_buffers stateM.good buffersM (-1), accountM, bytesF, agreesM, endpointM, baseM,
      statusM, Or.inr rfl, encodingM.last_flush stateM.good (-1), checksumM, inputLedgerM, by simpa only [Nat.add_zero] using strategyEffect.trans finalEffect⟩
  · subst ret
    have readyM := (doneReady rfl).1
    obtain ⟨pb, buf, treesM, ledger, _balance⟩ := stateM.symbols
    have ysNil : ys = [] := by
      have count := ledger.count
      rw [symbols] at count
      apply List.length_eq_zero_iff.mp
      change 0 = 3 * ys.length at count
      omega
    subst ys
    have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + writtenS.length) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    obtain ⟨markerProduced, after, z', result, writtenT, run, stateA, buffersA, accountA, bytesA,
        encodingA, _configA, statusA, lastA, adlerA, endpointA, _availableA, intervalA,_rest⟩ :=
      public_strategy_foreign_sync_done_raw_encoding (stateM.buffered endM controls.empty_cursor)
        buffersM treesM pointerM readyM encodingM
    have previousBytes : Bytes after z.next_out writtenS.length writtenS := by
      rw [pointer] at bytesM ⊢
      exact intervalA.keep_published_bytes bytesM
    have currentBytes : Bytes after (.ref (.dstate_depth owner) (oo + writtenS.length)) markerProduced writtenT := by
      rw [pointerM] at bytesA
      exact bytesA
    have allBytes := generic_published_bytes_append (by simpa only [pointer] using previousBytes) currentBytes
    have tailLength := public_bytes_length bytesA
    have account : StreamAccounting z z' used (writtenS ++ writtenT).length := by
      simpa only [List.length_append, tailLength, Nat.add_zero] using stream_accounting_trans accountM accountA
    refine ⟨used, after, z', result, extended, nextOrigin, middleBase, [], writtenS ++ writtenT,
      sourceRun.trans run, stateA, buffersA, account, ?_, agreesM, ?_, baseM, statusA.trans statusM, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_append, tailLength, pointer] using allBytes
    · rw [endpointA]; exact endpointM
    · rcases lastA with same | retry
      · exact Or.inl (same.trans controls.last_flush)
      · exact Or.inr retry
    · simpa only [List.append_assoc] using encodingA
    · rw [endpointA]; exact adlerA.trans checksumM
    · rw [endpointA]; exact inputLedgerM
    · simpa only [List.length_append, tailLength] using strategyEffect.trans intervalA

/-- Projection of the stronger exact caller-interval refinement. -/
theorem public_foreign_busy_sync_data_raw_prefix_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
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
      publicDataTail (some r) (some (.tab ds)) Z_SYNC_FLUSH h = .ok (Z_OK, after) ∧
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
  obtain ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
      statusA, lastA, encodingA, checksumA, inputLedgerA, _intervalA⟩ :=
    public_foreign_busy_sync_data_raw_prefix_input_interval boundary frontier buffers status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
  exact ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    statusA, lastA, encodingA, checksumA, inputLedgerA⟩

end Zlib.Deflate.Engine.Proofs
