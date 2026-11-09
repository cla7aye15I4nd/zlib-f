import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-input-ledger»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-final-effects»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-stream»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.finish-input-ledger»

/-! # Actual FINISH encoding and checksum match the consumed caller input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual FINISH strategy call includes the terminating
loop, every early output return, EOF settlement, insertion reset and final
block publication. The returned caller slice is exact on its final heap.
An output stop retains composable independent block meaning; actual EOF
completes a valid raw stream including any remaining pending bytes. Its logical accepted input equals the old prefix followed by the consumed original caller bytes.
Incoming prefix premises are mathematical encoding history, not callee
contracts. All output capacities, including zero strategy-entry space after a complete header, are admitted. Public wrapper/history composition follows separately. -/
theorem default_foreign_deflate_slow_finish_ready_stream_input_phase {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {before completed : List Bool} {previous : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (held : PendingBits h d before)
    (wirePrefix : ZlibF.Spec.bytesToBits previous ++ before = completed)
    (prefixMeaning : BlockPrefix [] 0 [] completed (inputPrefix input base)) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      inputPrefix extended (origin + fillEnd d + used) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (origin + fillEnd d + used))).toUInt64 ∧
      ((rc = need_more ∧ ∃ remaining encoded,
        StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
        nextOrigin + fillEnd result = origin + fillEnd d + used ∧
        PendingBits after result remaining ∧
        ZlibF.Spec.bytesToBits (previous ++ written) ++ remaining = encoded ∧
        BlockPrefix [] 0 [] encoded (inputPrefix extended base') ∧
        encoded.length % 8 = result.bi_valid.toInt.toNat % 8) ∨
       ((rc = finish_started ∨ rc = finish_done) ∧ ∃ tailBytes,
        Bytes after result.pending_out result.pending.toNat tailBytes ∧ result.bi_valid.toInt.toNat = 0 ∧
        ZlibF.Spec.Deflate.Valid (inputPrefix extended (origin + fillEnd d + used))
          (previous ++ written ++ tailBytes))) := by
  have ready := publish
  have position : completed.length % 8 = d.bi_valid.toInt.toNat % 8 := by
    have count := congrArg List.length wirePrefix
    have pendingLength := pending_bits_exact_length held
    simp only [List.length_append, encoded_bytes_length] at count
    omega
  obtain ⟨_oldUsed, _oldProduced, final, middle, oldZ, oldD, _oldBase, _oldSymbols, _oldInput, _oldOrigin,
      loopRun, oldBoundary, _oldEnd, _oldBuffers, _oldAccount, _oldAgrees, _oldEndpoint,
      _oldBaseLe, stopped, _oldFull, eof, _oldReady⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  obtain ⟨used, currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols,
      beforeL, loopWritten, remaining, blockBits, stateL, endL, buffersL, accountL,
      agreesL, endpointL, _baseL, pendingBeforeL, bytesL, pendingL, wireL, prefixL, positionL, checksumL, inputLedgerL⟩ :=
    default_foreign_slow_loop_run_block_prefix_input (offset := completed.length) boundary frontier buffers positive pointer memory wrap publish inputValid snapshot checksum position loopRun
  have streamEq : oldZ = currentZ := Option.some.inj (oldBoundary.good.live.hz.symm.trans stateL.good.live.hz)
  have stateEq : oldD = currentD := Option.some.inj (oldBoundary.good.live.hs.symm.trans stateL.good.live.hs)
  rw [stateEq, streamEq] at eof
  rw [endpointL] at checksumL inputLedgerL
  have beforeEq : beforeL = before :=
    (pending_bits_zero_value ready.1 pendingBeforeL).trans (pending_bits_zero_value ready.1 held).symm
  rw [beforeEq] at wireL
  have prefixStep : BlockPrefix [] (0 + completed.length) (inputPrefix input base) blockBits (inputPrefix currentInput currentBase) := by
    simpa only [Nat.zero_add] using prefixL
  have prefixAll := block_prefix_append prefixMeaning prefixStep
  have wireAll : ZlibF.Spec.bytesToBits (previous ++ loopWritten) ++ remaining = completed ++ blockBits := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireL wirePrefix ⊢
    rw [wireL, ← List.append_assoc, wirePrefix]
  rcases stopped with returned | ⟨running, broke⟩
  · have actual : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, middle) := by
      rw [deflate_slow_eof_tail_source, bind_app, loopRun]
      simp only [returned, pure_app]
    refine ⟨used, need_more, middle, currentZ, currentD, currentInput, currentOrigin,
      currentBase, currentSymbols, loopWritten, actual, stateL.toContentBoundary,
      buffersL, accountL, bytesL, agreesL, inputLedgerL, checksumL, Or.inl ⟨rfl, remaining, completed ++ blockBits,
      stateL, endL, endpointL, pendingL, wireAll, prefixAll, ?_⟩⟩
    simpa only [List.length_append] using positionL
  · have emptyL := (eof broke).1
    have inputEmptyL := (eof broke).2
    have publishL : PublishReady currentD := by
      simpa only [stateEq] using _oldReady running
    have selfConfig : StrategyBoundary middle r ds currentZ currentD currentInput currentOrigin currentBase currentSymbols (engineConfig currentD) := by
      rw [stateL.configuration]
      exact stateL
    have positiveL : 0 < currentD.level.toInt := by
      have level := congrArg EngineConfig.level stateL.configuration
      change currentD.level = config.level at level
      rw [level]
      exact positive
    have memoryL : currentD.lit_bufsize.toNat = 16384 := by
      have field := congrArg EngineConfig.memory stateL.configuration
      change currentD.lit_bufsize = config.memory at field
      rw [field]
      exact memory
    have wrapL : currentD.wrap = 1 := (congrArg EngineConfig.wrap stateL.configuration).trans wrap
    have pointerL : currentZ.next_out = .ref (.dstate_depth owner) (oo + loopWritten.length) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    obtain ⟨tailProduced, after, z', result, tailSymbols, tailWritten, tailBytes,
        tailRun, stateA, buffersA, accountA, bytesA, pendingBytes, finalA, validA,frameTail⟩ :=
      default_foreign_slow_eof_finish_tail_complete_stream selfConfig endL buffersL emptyL positiveL pointerL publishL.2.1 memoryL publishL.1 wrapL
        pendingL wireAll prefixAll
    have checksumA := default_foreign_slow_eof_finish_run_adler selfConfig endL buffersL emptyL positiveL pointerL publishL.2.1
      memoryL publishL.1 wrapL tailRun stateA.good.live.hz accountA
    have tailEffect : ByteOutputInterval middle after (.dstate_depth owner) (oo + loopWritten.length) tailProduced := by
      rw [pointerL] at frameTail
      exact ByteOutputInterval.of_buffer_frame frameTail
    have previousBytes : Bytes after z.next_out loopWritten.length loopWritten := by
      rw [pointer] at bytesL ⊢
      exact tailEffect.keep_published_bytes bytesL
    have newBytes : Bytes after (.ref (.dstate_depth owner) (oo + loopWritten.length)) tailProduced tailWritten := by
      rw [pointerL] at bytesA
      exact bytesA
    have bothBytes := generic_published_bytes_append (by simpa only [pointer] using previousBytes) newBytes
    have tailLength := public_bytes_length bytesA
    have account : StreamAccounting z z' used (loopWritten ++ tailWritten).length := by
      simpa only [List.length_append, tailLength, Nat.add_zero] using stream_accounting_trans accountL accountA
    have endIndex : currentOrigin + currentD.strstart.toNat = origin + fillEnd d + used := by
      simpa only [fillEnd, emptyL, UInt32.toNat_zero, Nat.add_zero] using endpointL
    rw [endIndex] at validA
    have actual : deflate_slow (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) := by
      rw [deflate_slow_eof_tail_source, bind_app, loopRun]
      simp only [running]
      exact tailRun
    refine ⟨used, if z'.avail_out == 0 then finish_started else finish_done,
      after, z', result, currentInput, currentOrigin, currentBase + represented tailSymbols,
      [], loopWritten ++ tailWritten, actual, stateA, buffersA, account,
      ?_, agreesL, inputLedgerL, checksumA.trans checksumL, Or.inr ⟨?_, tailBytes, pendingBytes, finalA, ?_⟩⟩
    · simpa only [List.length_append, tailLength, pointer] using bothBytes
    · split <;> simp only [true_or, or_true]
    · simpa only [List.append_assoc] using validA

end Zlib.Deflate.Engine.Proofs
