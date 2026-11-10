import ZlibF.Proof.«deflate.c.engine.public-nonfinal-ready-encoding»
import ZlibF.Proof.«deflate.c.engine.public-nonfinal-data-interval»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-input»
import ZlibF.Proof.«deflate.c.engine.valid-pending-entry»

/-! # Every accepted BUSY nonfinal request encodes its actual input and output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete actual BUSY requests for every valid non-FINISH flag retain
raw meaning and Adler of exactly the consumed original input. Old pending
may exhaust output or drain and continue into compression. The actual
rank check and empty-input duplicate refusals are covered when pending is
empty; the check is not repeated after a drain. Positive raw output is
required here. Early entry refusals and initial headers remain separate. -/
theorem public_busy_nonfinal_accepted_raw_prefix_input {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate (some r) flush h = .ok (rc, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR) ∧ result.status = BUSY_STATE ∧ (result.last_flush = flush ∨ result.last_flush = -1) ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases queued : d.pending = 0
  · exact public_busy_nonfinal_ready_raw_prefix_input boundary buffers status level strategy pointer memory wrap queued output
      inputValid lower upper flush flag snapshot checksum encoding
  · obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, written, remaining, _base,
        run, stateA, buffersA, accountA, _sizes, _storage, _outputA, lastA, _count,
        _bits, fields, bytesA, pendingA, wireA, adlerA⟩ :=
        public_pending_buffered_exhausted_adler flush boundary buffers pointer inputValid
          flagLo flagHi (by intro impossible; rw [status] at impossible; cases impossible) output enough pending
      have length := public_bytes_length bytesA
      have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
        rw [wireA, wire]
      have endA : fillEnd result = fillEnd d := by rw [fields]; rfl
      have checksumA : z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
        rw [endA, adlerA]
        exact checksum
      refine ⟨0, Z_OK, after, z', result, input, origin, base, xs, written, run, stateA,
        buffersA, ?_, ?_, fun _ _ => rfl, ?_, Nat.le_refl _, Or.inl rfl, ?_, Or.inr lastA,
        ⟨remaining, encoded, pendingA, wireAll, meaning⟩, checksumA, by simp only [endA, List.take_zero, List.append_nil]⟩
      · rw [length]; exact accountA
      · rw [length]; exact bytesA
      · rw [fields]; rfl
      · rw [fields]; exact status
    · have boundary0 := last_flush_buffered_boundary boundary flush
      have buffers0 := last_flush_buffers boundary.good buffers flush
      have pending0 := last_flush_pending_bits boundary.good pending flush
      obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
          flushRun, stateM, buffersM, accountM, _sizes, storageM, amountP, _leftP, fieldsM,
          readyM, bytesM, pendingM, wireM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have countP : producedP = d.pending.toNat := by
        change producedP = min d.pending.toNat z.avail_out.toNat at amountP
        rw [Nat.min_eq_left (by omega)] at amountP
        exact amountP
      have outputM : 0 < zm.avail_out.toNat := by
        have count := accountM.2.2.2.1
        omega
      have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
      have levelM : dm.level = 6 := by rw [fieldsM]; exact level
      have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
      have lastM : dm.last_flush = flush := by rw [fieldsM]
      have pointerM : zm.next_out = .ref (.blk ob) (oo + producedP) := by
        rw [accountM.2.2.2.2.2.1, pointer]
        rfl
      have wireP : ZlibF.Spec.bytesToBits (published ++ writtenP) ++ remainingP = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireM ⊢
        rw [wireM, wire]
      have encodingM : RawPrefix middle dm input base (published ++ writtenP) :=
        ⟨remainingP, encoded, pendingM, wireP, meaning⟩
      have validM := input_valid_accounting_output inputValid accountM
      have adlerM := flush_pending_low_run_adler boundary0.good buffers0 pointer boundary0.bits
        flushRun stateM.good.live.hz accountM
      have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd dm))).toUInt64 := by
        have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
        rw [endM, adlerM]
        exact checksum
      have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := flush }) boundary.good.live.hs rfl snapshot
      have snapshotM := flush_pending_low_input_snapshot boundary0.good buffers0 pointer boundary0.bits
        _baseP snapshot0 flushRun stateM.good.live.hz accountM storageM
      obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
          dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, statusA,
          lastA, encodingA, checksumA, inputLedgerA, effect⟩ :=
        public_busy_nonfinal_data_raw_prefix_input_interval stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM outputM) validM flush flag snapshotM checksumM encodingM
      have entry := public_pending_valid_continue boundary.good stateM.good status
        (by rw [pointer]; intro impossible; cases impossible)
        (by intro zero; rw [zero] at output; contradiction) inputValid queued flush flagLo flagHi flushRun
        (by intro zero; rw [zero] at outputM; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases impossible)
      have actual := entry.trans ((public_busy_header_skip_next stateM.good statusM
        (publicDataTail (some r) (some (.tab ds)) flush)).trans dataRun)
      have lengthP := public_bytes_length bytesM
      have earlier : Bytes after z.next_out producedP writtenP := by
        rw [pointer] at bytesM ⊢
        have effectP : RawOutputInterval middle after ob (oo + producedP) written.length := effect
        rw [← lengthP] at effectP
        have oldBytes : Bytes middle (.ref (.blk ob) oo) writtenP.length writtenP := by rw [lengthP]; exact bytesM
        simpa only [lengthP] using effectP.keep_published_bytes oldBytes
      have newBytes : Bytes after (.ref (.blk ob) (oo + producedP)) written.length written := by
        rw [pointerM] at bytesA
        exact bytesA
      have combinedBytes := published_bytes_append (by simpa only [pointer] using earlier) newBytes
      have account : StreamAccounting z z' used (writtenP ++ written).length := by
        simpa only [List.length_append, lengthP, Nat.zero_add] using stream_accounting_trans accountM accountA
      have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
      have agrees : ∀ i, i < origin + fillEnd d → nextInput i = input i := by
        simpa only [endM] using agreesA
      have endpoint : nextOrigin + fillEnd result = origin + fillEnd d + used := by
        simpa only [endM] using endpointA
      rw [lastM] at lastA
      refine ⟨used, Z_OK, after, z', result, nextInput, nextOrigin, nextBase, ys, writtenP ++ written,
        actual, stateA, buffersA, account, ?_, agrees, endpoint, baseA, Or.inl rfl, statusA, lastA, ?_, checksumA, by simpa only [endM] using inputLedgerA⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using encodingA


end Zlib.Deflate.Engine.Proofs
