import ZlibF.Proof.«deflate.c.borrow-stable-publish»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-observed-api»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-finish-accepted-shared»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-data-completed»
import ZlibF.Proof.«deflate.c.engine.public-finish-accepted-representation»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual accepted foreign FINISH retains its correlated working or completed encoding phase. -/
theorem public_foreign_busy_finish_accepted_completed_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
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
  · exact public_foreign_busy_finish_ready_completed_encoding boundary buffers status level strategy pointer memory wrap
      queued output lower upper inputValid snapshot checksum encoding
  · obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, written, remaining, _base,
        run, stateA, buffersA, accountA, _sizes, _storage, _outputA, _lastA, _count,
        _bits, fields, bytesA, pendingA, wireA, adlerA, _pendingFrameA⟩ :=
        public_pending_buffered_exhausted_foreign_adler Z_FINISH boundary buffers pointer inputValid
          (by decide) (by decide) (fun _ => rfl) output enough pending
      have length := caller_bytes_length bytesA
      have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
        rw [wireA, wire]
      have endA : fillEnd result = fillEnd d := by rw [fields]; rfl
      refine ⟨0, Z_OK, after, z', result, written, inputPrefix input (origin + fillEnd d),
        by simp, run, stateA.good, buffersA, ?_, ?_, adlerA.trans checksum,
        Or.inl ⟨input, origin, base, xs, stateA, (by rw [fields];exact status), ⟨remaining, encoded, pendingA, wireAll, meaning⟩, ?_⟩, ?_⟩
      · rw [length]; exact accountA
      · rw [length]; exact bytesA
      · rw [endA]
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
      have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
      obtain ⟨_pb,producedP,middle,zm,dm,writtenP,remainingP,baseP,flushRun,entry,stateM,buffersM,accountM,
          _sizes,storageM,_amountP,outputM,readyM,statusM,_lastM,fieldsM,bytesM,pendingM,wireM,frameM⟩ :=
        public_pending_buffered_continue_foreign boundary buffers pointer inputValid status queued (by omega)
          Z_FINISH (Or.inr rfl) pending
      have levelM : dm.level = 6 := by rw [fieldsM];exact level
      have strategyM : dm.strategy = 0 := by rw [fieldsM];exact strategy
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + producedP) := by
        rw [accountM.2.2.2.2.2.1,pointer]
        rfl
      have wireP : ZlibF.Spec.bytesToBits (published ++ writtenP) ++ remainingP = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireM ⊢
        rw [wireM, wire]
      have encodingM : RawPrefix middle dm input base (published ++ writtenP) :=
        ⟨remainingP, encoded, pendingM, wireP, meaning⟩
      have validM := input_valid_accounting_output inputValid accountM
      have adlerM := (flush_pending_low_foreign_run_scalar_effects boundary0.good buffers0 pointer boundary0.bits
        flushRun stateM.good.live.hz accountM).1
      have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
      have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd dm))).toUInt64 := by
        rw [endM, adlerM]
        exact checksum
      have snapshotM : Bytes middle zm.next_in zm.avail_in.toNat actualInput := by
        have initialBuffers:=buffers
        obtain ⟨oldZ,oldGet,range,_outputRange,separated⟩ := initialBuffers
        have oldEq : oldZ=z := Option.some.inj (oldGet.symm.trans boundary.good.live.hz)
        subst oldZ
        have precise : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
            [⟨z.next_out,producedP⟩] :=
          ⟨full_frame_weaken frameM.1 (by intro b changed;rcases changed with root|own;exact Or.inl root;exact Or.inr (Or.inl own)),frameM.2⟩
        have separateNow : Separate z.next_in z.avail_in.toNat z.next_out producedP := by
          simpa only [advance_zero] using separate_advance_right (used := 0) separated
            (by have count:=accountM.2.2.2.1;omega)
        have kept := foreign_caller_input_bytes_preserved boundary.good buffers pointer range separateNow
          (Nat.le_refl _) snapshot precise ((Zlib.Deflate.BorrowProofs.stable_flush_pending _ _ _ _ flushRun).trans (by rfl))
        have inputPointer : zm.next_in=z.next_in := by simpa only [advance_zero] using accountM.2.2.2.2.1
        have inputCount : zm.avail_in=z.avail_in := UInt32.toNat_inj.mp (by have count:=accountM.2.2.1;omega)
        rw [inputPointer,inputCount]
        exact kept
      obtain ⟨used, rc, after, z', result, written, accepted, acceptedA, dataRun, goodA, buffersA,
          accountA, bytesA, checksumA, phasesA, endedA⟩ :=
        public_foreign_busy_finish_data_completed_encoding stateM buffersM statusM levelM strategyM pointerM memory wrap
          readyM validM snapshotM checksumM encodingM
      have actual := entry.trans dataRun
      have effect := public_foreign_busy_finish_data_run_output_interval stateM buffersM statusM levelM strategyM
        pointerM memory wrap readyM validM dataRun goodA.live.hz accountA
      have lengthP := caller_bytes_length bytesM
      have earlier : Bytes after z.next_out producedP writtenP := by
        rw [pointer] at bytesM ⊢
        have effectP : ByteOutputInterval middle after (.dstate_depth owner) (oo + producedP) written.length := effect
        rw [← lengthP] at effectP
        have oldBytes : Bytes middle (.ref (.dstate_depth owner) oo) writtenP.length writtenP := by rw [lengthP]; exact bytesM
        simpa only [lengthP] using effectP.keep_published_bytes oldBytes
      have current : Bytes after (.ref (.dstate_depth owner) (oo + producedP)) written.length written := by
        rw [pointerM] at bytesA
        exact bytesA
      have combinedBytes := generic_published_bytes_append (by simpa only [pointer] using earlier) current
      have account : StreamAccounting z z' used (writtenP ++ written).length := by
        simpa only [List.length_append, lengthP, Nat.zero_add] using stream_accounting_trans accountM accountA
      refine ⟨used, rc, after, z', result, writtenP ++ written, accepted,
        by simpa only [endM] using acceptedA, actual, goodA, buffersA, account, ?_, checksumA, ?_, ?_⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using phasesA
      · intro ended
        simpa only [List.append_assoc] using endedA ended


end Zlib.Deflate.Engine.Proofs
