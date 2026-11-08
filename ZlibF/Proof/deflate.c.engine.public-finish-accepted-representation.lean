import ZlibF.Proof.«deflate.c.engine.public-finish-ready-representation»
import ZlibF.Proof.«deflate.c.engine.public-pending-checksum»

/-! # Every accepted raw-phase BUSY FINISH call retains exact input and encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual accepted BUSY FINISH call includes old pending
output exhausting the caller buffer, pending drain followed by compression,
final-block publication and the one-time zlib trailer. Encoding refers to
exactly the consumed original caller input. STREAM_END gives independent
zlib validity for the cumulative published bytes. All positive raw output
capacities are admitted; header and finished-state phases are separate. -/
theorem public_busy_finish_accepted_completed_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result written accepted,
      accepted = inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase (published ++ written) ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ FinishedEncoding after result accepted (published ++ written))) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written)) := by
  by_cases queued : d.pending = 0
  · exact public_busy_finish_ready_completed_encoding boundary buffers status level strategy pointer memory wrap
      queued output lower upper inputValid snapshot checksum encoding
  · obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, written, remaining, _base,
        run, stateA, buffersA, accountA, _sizes, _storage, _outputA, _lastA, _count,
        _bits, fields, bytesA, pendingA, wireA, adlerA⟩ :=
        public_pending_buffered_exhausted_adler Z_FINISH boundary buffers pointer inputValid
          (by decide) (by decide) (fun _ => rfl) output enough pending
      have length := caller_bytes_length bytesA
      have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
        rw [wireA, wire]
      have endA : fillEnd result = fillEnd d := by rw [fields]; rfl
      refine ⟨0, Z_OK, after, z', result, written, inputPrefix input (origin + fillEnd d),
        by simp, run, stateA.good, buffersA, ?_, ?_, adlerA.trans checksum,
        Or.inl ⟨input, origin, base, xs, stateA, (by rw [fields]; exact status),
          ⟨remaining, encoded, pendingA, wireAll, meaning⟩, ?_⟩, ?_⟩
      · rw [length]; exact accountA
      · rw [length]; exact bytesA
      · rw [endA]
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
      have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
      have pending0 := last_flush_pending_bits boundary.good pending Z_FINISH
      obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, baseP,
          flushRun, stateM, buffersM, accountM, _sizes, storageM, amountP, _leftP, fieldsM,
          readyM, bytesM, pendingM, wireM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have outputM : 0 < zm.avail_out.toNat := by
        have count := accountM.2.2.2.1
        change producedP = min d.pending.toNat z.avail_out.toNat at amountP
        rw [Nat.min_eq_left (by omega)] at amountP
        omega
      have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
      have levelM : dm.level = 6 := by rw [fieldsM]; exact level
      have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
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
      have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
      have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd dm))).toUInt64 := by
        rw [endM, adlerM]
        exact checksum
      have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_FINISH }) boundary.good.live.hs rfl snapshot
      have snapshotM := flush_pending_low_input_snapshot boundary0.good buffers0 pointer boundary0.bits
        baseP snapshot0 flushRun stateM.good.live.hz accountM storageM
      obtain ⟨used, rc, after, z', result, written, accepted, acceptedA, dataRun, goodA, buffersA,
          accountA, bytesA, checksumA, phasesA, endedA⟩ :=
        public_busy_finish_data_completed_encoding stateM buffersM statusM levelM strategyM pointerM memory wrap
          (readyM outputM) validM snapshotM checksumM encodingM
      have entry := public_pending_finish_continue boundary.good stateM.good
        (by rw [pointer]; intro impossible; cases impossible)
        (by intro zero; rw [zero] at output; contradiction) inputValid queued flushRun
        (by intro zero; rw [zero] at outputM; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have actual := entry.trans ((public_busy_header_skip stateM.good statusM).trans dataRun)
      obtain ⟨_effectUsed, _effectProduced, _effectRc, _other, _otherZ, _otherD, effectRun, effectGood,
          effectAccount, _effectInput, _effectOutput, outputEffect⟩ :=
        public_busy_slow_finish_output_execution (stateM.strategy (readyM outputM)) stateM.end_frontier buffersM
          statusM levelM strategyM pointerM memory wrap (readyM outputM) validM
      have effect : RawOutputInterval middle after ob (oo + producedP) written.length :=
        RawOutputInterval.identify effectRun dataRun effectGood.live.hz goodA.live.hz effectAccount accountA outputEffect
      have lengthP := caller_bytes_length bytesM
      have earlier : Bytes after z.next_out producedP writtenP := by
        rw [pointer] at bytesM ⊢
        have effectP : RawOutputInterval middle after ob (oo + producedP) written.length := effect
        rw [← lengthP] at effectP
        have oldBytes : Bytes middle (.ref (.blk ob) oo) writtenP.length writtenP := by rw [lengthP]; exact bytesM
        simpa only [lengthP] using effectP.keep_published_bytes oldBytes
      have current : Bytes after (.ref (.blk ob) (oo + producedP)) written.length written := by
        rw [pointerM] at bytesA
        exact bytesA
      have combinedBytes := published_bytes_append (by simpa only [pointer] using earlier) current
      have account : StreamAccounting z z' used (writtenP ++ written).length := by
        simpa only [List.length_append, lengthP, Nat.zero_add] using stream_accounting_trans accountM accountA
      refine ⟨used, rc, after, z', result, writtenP ++ written, accepted,
        by simpa only [endM] using acceptedA, actual, goodA, buffersA, account, ?_, checksumA, ?_, ?_⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using phasesA
      · intro ended
        simpa only [List.append_assoc] using endedA ended

end Zlib.Deflate.Engine.Proofs
