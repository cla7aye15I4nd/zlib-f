import ZlibF.Proof.«deflate.c.engine.common-finish-data-representation»
import ZlibF.Proof.«deflate.c.engine.common-header-drain-checksum»

/-! # Actual split-header FINISH resumption enters complete encoded compression -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- With room beyond the remaining level-specific header byte, actual FINISH
resumption emits that byte then performs complete compression and trailer
publication. The logical accepted input is exactly the consumed original
caller snapshot. No raw encoding seed is assumed: draining the actual
header establishes the empty raw phase. -/
theorem public_common_header_finish_continue_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (room : 1 < z.avail_out.toNat)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 []).toUInt64) (encoding : CommonHeaderPending h d config.level [120]) :
    ∃ used rc after z' result rawWritten accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([(levelHeaderWord config.level &&& 0xff).toUInt8] ++ rawWritten) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase rawWritten ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ CommonFinishedEncoding after result config.level accepted rawWritten)) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix config.level ++ rawWritten)) := by
  have shape := encoding.one_remaining
  have headerEncoding := encoding
  obtain ⟨_held, _pendingBytes, _headerEq, headerBits, headerStart, headerLook⟩ := headerEncoding
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  have pending0 := last_flush_pending_bits boundary.good shape.2 Z_FINISH
  obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, baseP,
      flushRun, stateM, buffersM, accountM, _sizes, storageM, amountP, leftP, fieldsM,
      readyM, bytesM, pendingM, wireM⟩ :=
    flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
  have countP : producedP = 1 := by
    change producedP = min d.pending.toNat z.avail_out.toNat at amountP
    rw [shape.1, Nat.min_eq_left (by omega)] at amountP
    exact amountP
  have emptyM : dm.pending.toNat = 0 := by
    change dm.pending.toNat + producedP = d.pending.toNat at leftP
    rw [shape.1, countP] at leftP
    omega
  have bitsM : dm.bi_valid.toInt.toNat = 0 := by rw [fieldsM]; exact headerBits
  obtain ⟨writtenEq, encodingM⟩ := common_header_byte_drain_encoding (input := input) pendingM emptyM bitsM wireM
  have outputM : 0 < zm.avail_out.toNat := by
    have count := accountM.2.2.2.1
    rw [countP] at count
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
  have lowM : 4 ≤ dm.level.toInt := by rw [fieldsM]; exact low
  have highM : dm.level.toInt ≤ 9 := by rw [fieldsM]; exact high
  have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
  have pointerM : zm.next_out = .ref (.blk ob) (oo + producedP) := by
    rw [accountM.2.2.2.2.2.1, pointer]
    rfl
  have validM := input_valid_accounting_output valid accountM
  have adlerM := flush_pending_low_run_adler boundary0.good buffers0 pointer boundary0.bits
    flushRun stateM.good.live.hz accountM
  have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
  have prefixEmpty : inputPrefix input (0 + fillEnd dm) = [] := by
    rw [endM]
    simp only [fillEnd, headerStart, headerLook, UInt32.toNat_zero, Nat.add_zero,
      inputPrefix, List.range_zero, List.map_nil]
  have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd dm))).toUInt64 := by
    rw [prefixEmpty, adlerM]
    exact checksum
  have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_FINISH }) boundary.good.live.hs rfl snapshot
  have snapshotM := flush_pending_low_input_snapshot boundary0.good buffers0 pointer boundary0.bits
    baseP snapshot0 flushRun stateM.good.live.hz accountM storageM
  obtain ⟨used, rc, after, z', result, rawWritten, accepted, acceptedA, dataRun, goodA, buffersA,
      accountA, bytesA, checksumA, phasesA, endedA⟩ :=
    public_common_slow_finish_data_completed_encoding stateM buffersM statusM lowM highM strategyM pointerM memory wrap
      (readyM outputM) validM snapshotM checksumM encodingM
  have acceptedEq : accepted = actualInput.take used := by simpa only [prefixEmpty, List.nil_append] using acceptedA
  have queued : d.pending ≠ 0 := by intro zero; rw [zero] at shape; simp at shape
  have entry := public_pending_finish_continue boundary.good stateM.good
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at room; contradiction) valid queued flushRun
    (by intro zero; rw [zero] at outputM; contradiction)
    (by intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
  have actual := entry.trans ((public_busy_header_skip stateM.good statusM).trans dataRun)
  obtain ⟨_effectUsed, _effectProduced, _effectRc, _other, _otherZ, _otherD, effectRun, effectGood,
      effectAccount, _effectInput, _effectOutput, outputEffect⟩ :=
    public_common_slow_finish_output_execution (stateM.strategy (readyM outputM)) stateM.end_frontier buffersM
      statusM lowM highM strategyM pointerM memory wrap (readyM outputM) validM
  have effect : RawOutputInterval middle after ob (oo + producedP) rawWritten.length :=
    RawOutputInterval.identify effectRun dataRun effectGood.live.hz goodA.live.hz effectAccount accountA outputEffect
  have earlier : Bytes after (.ref (.blk ob) oo) 1 [(levelHeaderWord config.level &&& 0xff).toUInt8] := by
    have oldBytes : Bytes middle (.ref (.blk ob) oo) [(levelHeaderWord config.level &&& 0xff).toUInt8].length [(levelHeaderWord config.level &&& 0xff).toUInt8] := by
      simpa only [pointer, countP, writtenEq, List.length_cons, List.length_nil] using bytesM
    have kept : RawOutputInterval middle after ob (oo + [(levelHeaderWord config.level &&& 0xff).toUInt8].length) rawWritten.length := by
      simpa only [List.length_cons, List.length_nil, countP] using effect
    exact kept.keep_published_bytes oldBytes
  have current : Bytes after (.ref (.blk ob) (oo + 1)) rawWritten.length rawWritten := by
    simpa only [pointerM, countP] using bytesA
  have combinedBytes := published_bytes_append earlier current
  have account : StreamAccounting z z' used (1 + rawWritten.length) := by
    simpa only [countP, Nat.zero_add] using stream_accounting_trans accountM accountA
  refine ⟨used, rc, after, z', result, rawWritten, accepted, acceptedEq, actual, goodA, buffersA,
    account, ?_, checksumA, ?_, ?_⟩
  · simpa only [List.length_cons, List.length_nil, pointer] using combinedBytes
  · simpa only [List.nil_append] using phasesA
  · intro ended
    simpa only [List.append_nil] using endedA ended

end Zlib.Deflate.Engine.Proofs
