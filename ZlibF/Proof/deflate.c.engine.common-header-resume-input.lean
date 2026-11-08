import ZlibF.Proof.«deflate.c.engine.common-header-drain-encoding»
import ZlibF.Proof.«deflate.c.engine.common-header-drain-checksum»
import ZlibF.Proof.«deflate.c.engine.common-busy-no-flush-input»

/-! # Actual split header resumption encodes the consumed original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- With room beyond the remaining header byte, the actual public
NO_FLUSH call completes that byte and enters real raw compression. The
header byte remains readable after the later strategy output. The actual input snapshot survives that header output and identifies precisely the consumed logical prefix. -/
theorem public_common_header_pending_no_flush_continue_encoding_input {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {headerLevel : Int32}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (room : 1 < z.avail_out.toNat)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : CommonHeaderPending h d headerLevel [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([(levelHeaderWord headerLevel &&& 0xff).toUInt8] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  have shape := encoding.one_remaining
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have pending0 := last_flush_pending_bits boundary.good shape.2 Z_NO_FLUSH
  obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
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
  have bitsM : dm.bi_valid.toInt.toNat = 0 := by
    rw [fieldsM]
    obtain ⟨_, _, _, bits, _, _⟩ := encoding
    exact bits
  obtain ⟨writtenEq, encodingM⟩ := common_header_byte_drain_encoding (input := input) pendingM emptyM bitsM wireM
  have outputM : 0 < zm.avail_out.toNat := by
    have count := accountM.2.2.2.1
    rw [countP] at count
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
  have lowM : 4 ≤ dm.level.toInt := by rw [fieldsM]; exact low
  have highM : dm.level.toInt ≤ 9 := by rw [fieldsM]; exact high
  have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
  have lastM : dm.last_flush = Z_NO_FLUSH := by rw [fieldsM]
  have pointerM : zm.next_out = .ref (.blk ob) (oo + producedP) := by
    rw [accountM.2.2.2.2.2.1, pointer]
    rfl
  have validM := input_valid_accounting_output inputValid accountM
  have adlerM := flush_pending_low_run_adler boundary0.good buffers0 pointer boundary0.bits
    flushRun stateM.good.live.hz accountM
  have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd dm))).toUInt64 := by
    have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
    rw [endM, adlerM]
    exact checksum
  have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_NO_FLUSH }) boundary.good.live.hs rfl snapshot
  have snapshotM := flush_pending_low_input_snapshot boundary0.good buffers0 pointer boundary0.bits
    _baseP snapshot0 flushRun stateM.good.live.hz accountM storageM
  obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
      dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, _baseA, statusA,
      lastA, encodingA, checksumA, inputLedgerA⟩ :=
    public_common_slow_no_flush_data_ready_raw_prefix_input stateM buffersM statusM lowM highM strategyM pointerM
      memory wrap (readyM outputM) validM snapshotM checksumM encodingM
  have queued : d.pending ≠ 0 := by intro zero; rw [zero] at shape; simp at shape
  have entry := public_pending_no_flush_continue boundary.good stateM.good status
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at room; contradiction) inputValid queued flushRun
    (by intro zero; rw [zero] at outputM; contradiction)
    (by intro impossible; rw [statusM] at impossible; cases impossible)
  have actual := entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans dataRun)
  obtain ⟨_effectUsed, _effectProduced, _other, _otherZ, _otherD, effectRun, effectGood,
      effectAccount, _inputEffect, _outputEffect, outputEffect⟩ :=
    public_common_slow_no_flush_output_execution stateM buffersM statusM lowM highM strategyM pointerM
      memory wrap (readyM outputM) validM
  have effect : RawOutputInterval middle after ob (oo + producedP) written.length :=
    RawOutputInterval.identify effectRun dataRun effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
  have earlier : Bytes after (.ref (.blk ob) oo) 1 [(levelHeaderWord headerLevel &&& 0xff).toUInt8] := by
    have oldBytes : Bytes middle (.ref (.blk ob) oo) [(levelHeaderWord headerLevel &&& 0xff).toUInt8].length [(levelHeaderWord headerLevel &&& 0xff).toUInt8] := by
      simpa only [pointer, countP, writtenEq, List.length_cons, List.length_nil] using bytesM
    have kept : RawOutputInterval middle after ob (oo + [(levelHeaderWord headerLevel &&& 0xff).toUInt8].length) written.length := by
      simpa only [List.length_cons, List.length_nil, countP] using effect
    exact kept.keep_published_bytes oldBytes
  have newBytes : Bytes after (.ref (.blk ob) (oo + 1)) written.length written := by
    simpa only [pointerM, countP] using bytesA
  have combinedBytes := published_bytes_append earlier newBytes
  have account : StreamAccounting z z' used (1 + written.length) := by
    simpa only [countP, Nat.zero_add] using stream_accounting_trans accountM accountA
  have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
  rw [lastM] at lastA
  refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
    actual, stateA, buffersA, account, ?_, ?_, ?_, statusA, lastA, ?_, checksumA, by simpa only [endM] using inputLedgerA⟩
  · simpa only [List.length_cons, List.length_nil, pointer] using combinedBytes
  · simpa only [endM] using agreesA
  · simpa only [endM] using endpointA
  · simpa only [List.nil_append] using encodingA


/-- The next accepted positive-output NO_FLUSH request after a one-byte
split header always emits its remaining header byte followed by its actual raw output. This
covers immediate output exhaustion and continuation into compression. -/
theorem public_common_header_pending_no_flush_encoding_input {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {headerLevel : Int32}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (output : 0 < z.avail_out.toNat)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : CommonHeaderPending h d headerLevel [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([(levelHeaderWord headerLevel &&& 0xff).toUInt8] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  by_cases one : z.avail_out.toNat = 1
  · obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA,
        _outA, statusA, lastA, _pendingA, encodingA, checksumA⟩ :=
      public_common_header_pending_one_output_encoding_adler Z_NO_FLUSH boundary buffers pointer inputValid status
        (UInt32.toNat_inj.mp one) (by decide) (by decide) checksum encoding
    have endA : fillEnd result = fillEnd d := by
      have shape := public_pending_buffered_exhausted Z_NO_FLUSH boundary buffers pointer inputValid
        (by decide) (by decide) (by intro impossible; rw [status] at impossible; cases impossible)
        output (by rw [one, encoding.one_remaining.1]; decide) encoding.one_remaining.2
      obtain ⟨_pb, other, otherZ, otherD, _written, _remaining, _base, otherRun,
        otherBoundary, _buffers, _account, _sizes, _storage, _output, _last, _count,
        _bits, fields, _bytes, _pending, _wire⟩ := shape
      have heapEq : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
      rw [heapEq] at otherBoundary
      have stateEq : otherD = result := Option.some.inj (otherBoundary.good.live.hs.symm.trans stateA.good.live.hs)
      rw [stateEq] at fields
      rw [fields]
      rfl
    refine ⟨0, after, z', result, input, origin, 0, [], [], run, stateA, buffersA,
      accountA, bytesA, fun _ _ => rfl, ?_, statusA, Or.inl lastA, encodingA, checksumA, by simp only [endA, List.take_zero, List.append_nil]⟩
    rw [endA, Nat.add_zero]
  · exact public_common_header_pending_no_flush_continue_encoding_input boundary buffers pointer inputValid
      status low high strategy memory wrap (by omega) snapshot checksum encoding

end Zlib.Deflate.Engine.Proofs
