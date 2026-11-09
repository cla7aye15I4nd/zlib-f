import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-eof-prefix»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-positive-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-input-ledger»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.nonfinal-stream-input»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual nonzero non-FINISH strategy retains independent
nonfinal block meaning, exact output bytes on its final heap and Adler of
exactly the consumed original caller input. It includes output stops,
deferred EOF settlement, insertion reset and optional block publication.
All strategy-entry output capacities are admitted. Public marker emission
and its surrounding header/pending guards are composed separately. -/
theorem default_foreign_deflate_slow_nonfinal_ready_stream_input {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {before completed : List Bool} {previous : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (held : PendingBits h d before)
    (wirePrefix : ZlibF.Spec.bytesToBits previous ++ before = completed)
    (prefixMeaning : BlockPrefix [] 0 [] completed (inputPrefix input base)) :
    ∃ used rc after z' result extended nextOrigin base' ys written remaining encoded,
      deflate_slow (some (.tab ds)) flush h = .ok (rc, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits (previous ++ written) ++ remaining = encoded ∧
      BlockPrefix [] 0 [] encoded (inputPrefix extended base') ∧
      encoded.length % 8 = result.bi_valid.toInt.toNat % 8 ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      ((rc = need_more ∧ z'.avail_out = 0) ∨
       (rc = block_done ∧ z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.sym_next = 0)) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,written.length⟩] := by
  have position : completed.length % 8 = d.bi_valid.toInt.toNat % 8 := by
    have count := congrArg List.length wirePrefix
    have pendingLength := pending_bits_exact_length held
    simp only [List.length_append, encoded_bytes_length] at count
    omega
  obtain ⟨_oldUsed, _oldProduced, final, middle, oldZ, oldD, _oldBase, _oldSymbols, _oldInput, _oldOrigin,
      loopRun, oldBoundary, _oldEnd, _oldBuffers, _oldAccount, _oldAgrees, _oldEndpoint,
      _oldBaseLe, stopped, stoppedOutput, eof, oldReady⟩ :=
    default_foreign_slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  obtain ⟨used, currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols,
      beforeL, loopWritten, remaining, blockBits, stateL, endL, buffersL, accountL,
      agreesL, endpointL, baseL, pendingBeforeL, bytesL, pendingL, wireL, prefixL, positionL, checksumL, inputLedgerL⟩ :=
    default_foreign_slow_loop_run_block_prefix_input (offset := completed.length) boundary frontier buffers positive pointer
      memory wrap publish inputValid snapshot checksum position loopRun
  have preciseL := default_foreign_slow_loop_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish inputValid
    loopRun stateL.good.live.hz accountL
  have shapeL := (default_foreign_slow_loop_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid loopRun).1
  have streamEq : oldZ = currentZ := Option.some.inj (oldBoundary.good.live.hz.symm.trans stateL.good.live.hz)
  have stateEq : oldD = currentD := Option.some.inj (oldBoundary.good.live.hs.symm.trans stateL.good.live.hs)
  rw [stateEq, streamEq] at eof
  have beforeEq : beforeL = before :=
    (pending_bits_zero_value publish.1 pendingBeforeL).trans (pending_bits_zero_value publish.1 held).symm
  rw [beforeEq] at wireL
  have prefixStep : BlockPrefix [] (0 + completed.length) (inputPrefix input base) blockBits (inputPrefix currentInput currentBase) := by
    simpa only [Nat.zero_add] using prefixL
  have prefixAll := block_prefix_append prefixMeaning prefixStep
  have wireAll : ZlibF.Spec.bytesToBits (previous ++ loopWritten) ++ remaining = completed ++ blockBits := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireL wirePrefix ⊢
    rw [wireL, ← List.append_assoc, wirePrefix]
  rcases stopped with returned | ⟨running, broke⟩
  · have actual : deflate_slow (some (.tab ds)) flush h = .ok (need_more, middle) := by
      rw [deflate_slow_eof_tail_source, bind_app, loopRun]
      simp only [returned, pure_app]
    refine ⟨used, need_more, middle, currentZ, currentD, currentInput, currentOrigin, currentBase,
      currentSymbols, loopWritten, remaining, completed ++ blockBits, actual, stateL, endL, buffersL,
      accountL, bytesL, agreesL, endpointL, baseL, pendingL, wireAll, prefixAll, ?_, checksumL, inputLedgerL,
      Or.inl ⟨rfl, ?_⟩,shapeL,preciseL⟩
    · simpa only [List.length_append] using positionL
    · simpa only [streamEq] using stoppedOutput returned
  · have emptyL := (eof broke).1
    have inputEmptyL := (eof broke).2
    have publishL : PublishReady currentD := by simpa only [stateEq] using oldReady running
    have selfConfig : StrategyBoundary middle r ds currentZ currentD currentInput currentOrigin currentBase currentSymbols (engineConfig currentD) := by
      rw [stateL.configuration]; exact stateL
    have positiveL : 0 < currentD.level.toInt := by
      have level := congrArg EngineConfig.level stateL.configuration
      change currentD.level = config.level at level
      rw [level]; exact positive
    have memoryL : currentD.lit_bufsize.toNat = 16384 := by
      have field := congrArg EngineConfig.memory stateL.configuration
      change currentD.lit_bufsize = config.memory at field
      rw [field]; exact memory
    have pointerL : currentZ.next_out = .ref (.dstate_depth owner) (oo + loopWritten.length) := by
      rw [accountL.2.2.2.2.2.1, pointer]; rfl
    have positionTail : (completed ++ blockBits).length % 8 = currentD.bi_valid.toInt.toNat % 8 := by
      simpa only [List.length_append] using positionL
    obtain ⟨tailProduced, ret, after, z', result, tailSymbols, tailBefore, tailWritten, tailRemaining, tailBits,
        tailRun, contentA, endA, buffersA, accountA, clearA, configA, lookA, startA, availableA,
        insertA, lowA, readyA, _symbolsA, pendingBeforeA, bytesA, pendingA, wireA, meaningA, positionA, returnsA, exhaustedA,checksumA,shapeA,preciseA⟩ :=
      default_foreign_slow_eof_nonfinal_block_prefix (offset := (completed ++ blockBits).length) selfConfig endL buffersL emptyL
        positiveL pointerL publishL.2.1 memoryL publishL.1 positionTail flush nonfinal
    have preciseTail := preciseA
    rw [pointerL] at preciseTail
    have tailEffect : ByteOutputInterval middle after (.dstate_depth owner) (oo+loopWritten.length) tailProduced :=
      ByteOutputInterval.of_buffer_frame preciseTail
    have previousBytes : Bytes after z.next_out loopWritten.length loopWritten := by
      rw [pointer] at bytesL ⊢; exact tailEffect.keep_published_bytes bytesL
    have newBytes : Bytes after (.ref (.dstate_depth owner) (oo + loopWritten.length)) tailProduced tailWritten := by
      rw [pointerL] at bytesA; exact bytesA
    have bothBytes := generic_published_bytes_append (by simpa only [pointer] using previousBytes) newBytes
    have tailLength := public_bytes_length bytesA
    have account : StreamAccounting z z' used (loopWritten ++ tailWritten).length := by
      simpa only [List.length_append, tailLength, Nat.add_zero] using stream_accounting_trans accountL accountA
    have endAeq : fillEnd result = fillEnd currentD := by
      simp only [fillEnd, lookA, startA, emptyL, UInt32.toNat_zero, Nat.add_zero]
    have nextEndpoint : currentOrigin + fillEnd result = origin + fillEnd d + used := by rw [endAeq]; exact endpointL
    have strictA : result.sym_next.toNat < result.sym_end.toNat := by
      obtain ⟨_pb, _buf, trees, ledger, _balance⟩ := contentA.symbols
      have count := ledger.count
      have extent := trees.base.sym_end
      have lower := trees.base.lit_lo
      simp only [List.length_nil, Nat.mul_zero] at count
      omega
    have stateA : StrategyBoundary after r ds z' result currentInput currentOrigin (currentBase + represented tailSymbols) [] config :=
      ⟨contentA, Eq.trans configA stateL.configuration, clearA, lowA, strictA, readyA⟩
    have tailBase : currentBase + represented tailSymbols = currentOrigin + currentD.strstart.toNat := by
      have counted := contentA.accounted
      simpa only [pendingCredit, availableA, ite_true, Nat.add_zero, represented, startA] using counted
    rw [← tailBase] at meaningA
    have tailPrefix : BlockPrefix [] (0 + (completed ++ blockBits).length)
        (inputPrefix currentInput currentBase) tailBits (inputPrefix currentInput (currentBase + represented tailSymbols)) := by
      simpa only [Nat.zero_add] using meaningA
    have sameBefore : tailBefore = remaining :=
      (pending_bits_zero_value publishL.1 pendingBeforeA).trans (pending_bits_zero_value publishL.1 pendingL).symm
    rw [sameBefore] at wireA
    have allWire : ZlibF.Spec.bytesToBits (previous ++ (loopWritten ++ tailWritten)) ++ tailRemaining =
        (completed ++ blockBits) ++ tailBits := by
      have wire := congrArg (fun bits : List Bool => bits ++ tailBits) wireAll
      simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireA wire ⊢
      rw [wireA]
      exact wire
    have actual : deflate_slow (some (.tab ds)) flush h = .ok (ret, after) := by
      rw [deflate_slow_eof_tail_source, bind_app, loopRun]
      simp only [running]; exact tailRun
    have owned := (show ConfigFrame d currentD from stateL.configuration.trans boundary.configuration.symm).owned (ds:=ds)
    rw [owned] at preciseA
    have shapeAll := shapeL.trans shapeA
    have preciseAll : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,(loopWritten++tailWritten).length⟩] := by
      obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
      rw [pointer] at preciseL
      rw [pointerL] at preciseA
      have composed := foreign_buffer_frame_adjacent preciseL preciseA shapeL shapeA boundary.good.uniq get
        (caller_foreign_owner_outside boundary.good buffers pointer)
      simpa only [List.length_append,tailLength,pointer] using composed
    refine ⟨used, ret, after, z', result, currentInput, currentOrigin, currentBase + represented tailSymbols,
      [], loopWritten ++ tailWritten, tailRemaining, (completed ++ blockBits) ++ tailBits,
      actual, stateA, endA, buffersA, account, ?_, agreesL, nextEndpoint,
      Nat.le_trans baseL (Nat.le_add_right _ _), pendingA, allWire,
      block_prefix_append prefixAll tailPrefix, ?_, ?_, ?_, ?_,shapeAll,preciseAll⟩
    · simpa only [List.length_append, tailLength, pointer] using bothBytes
    · simpa only [List.length_append] using positionA
    · rw [endAeq]; exact checksumA.trans checksumL
    · rw [endAeq]; exact inputLedgerL
    · rcases returnsA with more | done
      · exact Or.inl ⟨more, exhaustedA more⟩
      · have inputA : z'.avail_in = 0 := by
          apply UInt32.toNat_inj.mp
          have count := accountA.2.2.1
          rw [inputEmptyL] at count
          omega
        obtain ⟨_pb, _buf, _trees, ledger, _balance⟩ := contentA.symbols
        have zero : result.sym_next = 0 := UInt32.toNat_inj.mp (by simpa only [List.length_nil, Nat.mul_zero, UInt32.toNat_zero] using ledger.count)
        exact Or.inr ⟨done, inputA, lookA, zero⟩

end Zlib.Deflate.Engine.Proofs
