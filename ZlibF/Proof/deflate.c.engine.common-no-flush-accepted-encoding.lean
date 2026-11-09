import ZlibF.Proof.«deflate.c.engine.common-no-flush-ready-encoding»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-output»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # An accepted actual public NO_FLUSH request preserves raw encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual public deflate entry, last-flush store, BUSY header skip,
computed slow dispatch and return control retain independent raw encoding
on the exact same returned heap. Empty-input retry is included. This is the
accepted no-old-pending BUSY branch; duplicate/refusal, header creation and
old-pending branches remain separate public obligations. -/
theorem public_common_slow_no_flush_ready_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (pending : d.pending = 0) (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (resume : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result extended base' (published ++ written) := by
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have encoding0 := encoding.last_flush boundary.good Z_NO_FLUSH
  have ready : PublishReady { d with last_flush := Z_NO_FLUSH } :=
    ⟨pending, boundary.empty_cursor pending, boundary.bits⟩
  obtain ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
      statusA, lastA, encodingA⟩ :=
    public_common_slow_no_flush_data_ready_raw_prefix boundary0 buffers0 status low high strategy pointer memory wrap ready inputValid encoding0
  have entry := public_busy_no_flush_resuming_entry boundary.good status pending
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at output; contradiction) inputValid lower upper resume
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
    entry.trans run, stateA, buffersA, accountA, bytesA, agreesA, endpointA,
    baseA, statusA, lastA, encodingA⟩

/-- Every accepted actual BUSY NO_FLUSH request preserves independent
raw encoding, including full old-pending output, a partial drain followed
by real compression, new input and empty-input retry. The full caller slice
is retained on the same final heap. Duplicate requests and initial wrapper
header creation remain separate public branches. -/
theorem public_common_slow_no_flush_accepted_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result extended base' (published ++ written) := by
  by_cases queued : d.pending = 0
  · have resumed : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2 := by
      rcases resume with pending | input | retry | initial
      · exact False.elim (pending queued)
      · exact Or.inl input
      · exact Or.inr (Or.inl retry)
      · exact Or.inr (Or.inr initial)
    exact public_common_slow_no_flush_ready_raw_prefix boundary buffers status low high strategy queued pointer output memory wrap inputValid lower upper resumed encoding
  · obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, written, remaining, _base,
        run, stateA, buffersA, accountA, _sizes, _storage, _outputA, lastA, _count,
        _bits, fields, bytesA, pendingA, wireA⟩ :=
        public_pending_buffered_exhausted Z_NO_FLUSH boundary buffers pointer inputValid
          (by decide) (by decide) (by intro impossible; rw [status] at impossible; cases impossible) output enough pending
      have length := public_bytes_length bytesA
      have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
        rw [wireA, wire]
      refine ⟨0, after, z', result, input, origin, base, xs, written, run, stateA,
        buffersA, ?_, ?_, fun _ _ => rfl, ?_, Nat.le_refl _, ?_, Or.inl lastA,
        remaining, encoded, pendingA, wireAll, meaning⟩
      · rw [length]; exact accountA
      · rw [length]; exact bytesA
      · rw [fields]; rfl
      · rw [fields]; exact status
    · have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
      have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
      have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
          flushRun, stateM, buffersM, accountM, _sizes, _storage, amountP, _leftP, fieldsM,
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
      have lowM : 4 ≤ dm.level.toInt := by rw [fieldsM]; exact low
      have highM : dm.level.toInt ≤ 9 := by rw [fieldsM]; exact high
      have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
      have lastM : dm.last_flush = Z_NO_FLUSH := by rw [fieldsM]
      have pointerM : zm.next_out = .ref (.blk ob) (oo + producedP) := by
        rw [accountM.2.2.2.2.2.1, pointer]
        rfl
      have wireP : ZlibF.Spec.bytesToBits (published ++ writtenP) ++ remainingP = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireM ⊢
        rw [wireM, wire]
      have encodingM : RawPrefix middle dm input base (published ++ writtenP) :=
        ⟨remainingP, encoded, pendingM, wireP, meaning⟩
      have validM := input_valid_accounting_output inputValid accountM
      obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
          dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, statusA,
          lastA, encodingA⟩ :=
        public_common_slow_no_flush_data_ready_raw_prefix stateM buffersM statusM lowM highM strategyM pointerM memory wrap (readyM outputM) validM encodingM
      have entry := public_pending_no_flush_continue boundary.good stateM.good status
        (by rw [pointer]; intro impossible; cases impossible)
        (by intro zero; rw [zero] at output; contradiction) inputValid queued flushRun
        (by intro zero; rw [zero] at outputM; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases impossible)
      have actual := entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans dataRun)
      obtain ⟨effectUsed, effectProduced, other, otherZ, otherD, effectRun, effectGood,
          effectAccount, _inputEffect, _outputEffect, outputEffect⟩ :=
        public_common_slow_no_flush_output_execution stateM buffersM statusM lowM highM strategyM pointerM memory wrap (readyM outputM) validM
      have effect : RawOutputInterval middle after ob (oo + producedP) written.length :=
        RawOutputInterval.identify effectRun dataRun effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
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
      refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, writtenP ++ written,
        actual, stateA, buffersA, account, ?_, agrees, endpoint, baseA, statusA, lastA, ?_⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using encodingA

end Zlib.Deflate.Engine.Proofs
