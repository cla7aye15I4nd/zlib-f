import ZlibF.Proof.«deflate.c.engine.public-header-resume-encoding»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-checksum»

/-! # Actual split header resumption retains encoding and checksum together -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Every accepted flush with a one-byte caller buffer completes an actual
split header before dispatch. The public call consumes no input, writes
exactly 156 and establishes the empty raw phase on the same returned heap. -/
theorem public_header_pending_one_output_encoding_adler {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (flush : Int32) (boundary : BufferedBoundary h r ds z d input origin 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (one : z.avail_out = 1)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ after z' result,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [156] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      result.pending = 0 ∧ RawPrefix after result input 0 [] ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
  have shape := encoding.one_remaining
  obtain ⟨_pb, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, outputA, lastA, countA,
      _bits, fields, bytesA, pendingA, wireA, adlerA⟩ :=
    public_pending_buffered_exhausted_adler flush boundary buffers pointer inputValid flagLo flagHi
      (by intro impossible; rw [status] at impossible; cases impossible)
      (by rw [one]; decide) (by rw [one, shape.1]; decide) shape.2
  have empty : result.pending.toNat = 0 := by rw [one, shape.1] at countA; change result.pending.toNat + 1 = 1 at countA; omega
  have bits : result.bi_valid.toInt.toNat = 0 := by
    rw [fields]
    obtain ⟨_, _, _, bits, _, _⟩ := encoding
    exact bits
  obtain ⟨writtenEq, encodingA⟩ := header_byte_drain_encoding pendingA empty bits wireA
  have endA : fillEnd result = fillEnd d := by rw [fields]; rfl
  have checksumA : z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
    rw [endA, adlerA]
    exact checksum
  refine ⟨after, z', result, run, stateA, buffersA, ?_, ?_, outputA, ?_, lastA,
    UInt64.toNat_inj.mp empty, encodingA, checksumA⟩
  · simpa only [one, UInt32.toNat_one] using accountA
  · simpa only [one, UInt32.toNat_one, writtenEq] using bytesA
  · rw [fields]; exact status


/-- With room beyond the remaining header byte, the actual public
NO_FLUSH call completes that byte and enters real raw compression. The
header byte remains readable after the later strategy output. -/
theorem public_header_pending_no_flush_continue_encoding_adler {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (room : 1 < z.avail_out.toNat)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 := by
  have shape := encoding.one_remaining
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have pending0 := last_flush_pending_bits boundary.good shape.2 Z_NO_FLUSH
  obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
      flushRun, stateM, buffersM, accountM, _sizes, _storage, amountP, leftP, fieldsM,
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
  obtain ⟨writtenEq, encodingM⟩ := header_byte_drain_encoding (input := input) pendingM emptyM bitsM wireM
  have outputM : 0 < zm.avail_out.toNat := by
    have count := accountM.2.2.2.1
    rw [countP] at count
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
  have levelM : dm.level = 6 := by rw [fieldsM]; exact level
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
  obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
      dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, _baseA, statusA,
      lastA, encodingA, checksumA⟩ :=
    public_busy_no_flush_data_ready_raw_prefix_adler stateM buffersM statusM levelM strategyM pointerM
      memory wrap (readyM outputM) validM checksumM encodingM
  have queued : d.pending ≠ 0 := by intro zero; rw [zero] at shape; simp at shape
  have entry := public_pending_no_flush_continue boundary.good stateM.good status
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at room; contradiction) inputValid queued flushRun
    (by intro zero; rw [zero] at outputM; contradiction)
    (by intro impossible; rw [statusM] at impossible; cases impossible)
  have actual := entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans dataRun)
  obtain ⟨_effectUsed, _effectProduced, _other, _otherZ, _otherD, effectRun, effectGood,
      effectAccount, _inputEffect, _outputEffect, outputEffect⟩ :=
    public_busy_slow_no_flush_output_execution stateM buffersM statusM levelM strategyM pointerM
      memory wrap (readyM outputM) validM
  have effect : RawOutputInterval middle after ob (oo + producedP) written.length :=
    RawOutputInterval.identify effectRun dataRun effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
  have earlier : Bytes after (.ref (.blk ob) oo) 1 [156] := by
    have oldBytes : Bytes middle (.ref (.blk ob) oo) [156].length [156] := by
      simpa only [pointer, countP, writtenEq, List.length_cons, List.length_nil] using bytesM
    have kept : RawOutputInterval middle after ob (oo + [156].length) written.length := by
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
    actual, stateA, buffersA, account, ?_, ?_, ?_, statusA, lastA, ?_, checksumA⟩
  · simpa only [List.length_cons, List.length_nil, pointer] using combinedBytes
  · simpa only [endM] using agreesA
  · simpa only [endM] using endpointA
  · simpa only [List.nil_append] using encodingA


/-- The next accepted positive-output NO_FLUSH request after a one-byte
split header always emits 156 followed by its actual raw output. This
covers immediate output exhaustion and continuation into compression. -/
theorem public_header_pending_no_flush_encoding_adler {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (output : 0 < z.avail_out.toNat)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 := by
  by_cases one : z.avail_out.toNat = 1
  · obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA,
        _outA, statusA, lastA, _pendingA, encodingA, checksumA⟩ :=
      public_header_pending_one_output_encoding_adler Z_NO_FLUSH boundary buffers pointer inputValid status
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
      accountA, bytesA, fun _ _ => rfl, ?_, statusA, Or.inl lastA, encodingA, checksumA⟩
    rw [endA, Nat.add_zero]
  · exact public_header_pending_no_flush_continue_encoding_adler boundary buffers pointer inputValid
      status level strategy memory wrap (by omega) checksum encoding

/-- Legal caller replacement retains the unfinished header and checksum
of its unchanged logical input, even when output storage is replaced. -/
theorem rebuffer_header_encoding_checksum {h g : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config)
    (encoding : HeaderPending h d published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ BufferedBoundary g r ds z' d input origin 0 [] config ∧
      HeaderPending g d published ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
  obtain ⟨z', get, stateA⟩ := rebuffer_buffered_boundary boundary edit header
  have encodingA := encoding.rebuffer boundary.good edit
  obtain ⟨_fresh, _uniq, _globals, _frame, old, new, oldGet, newGet, fields⟩ := edit
  have oldEq : old = z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
  have newEq : new = z' := Option.some.inj (newGet.symm.trans get)
  subst old new
  refine ⟨z', get, stateA, encodingA, ?_⟩
  rw [fields]
  exact checksum

end Zlib.Deflate.Engine.Proofs
