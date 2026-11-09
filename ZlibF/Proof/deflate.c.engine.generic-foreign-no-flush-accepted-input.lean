import ZlibF.Proof.«deflate.c.borrow-stable-publish»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-data-effects»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-ready-joint-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-adler»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete accepted BUSY NO_FLUSH preserves exact input and output through queued bytes. -/
theorem public_foreign_busy_no_flush_accepted_joint_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (encoding : RawPrefix h d input base published)
    (checksum : z.adler=(ZlibF.Spec.adler32 (inputPrefix input (origin+fillEnd d))).toUInt64) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler=(ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin+fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin+fillEnd result)=inputPrefix input (origin+fillEnd d)++actualInput.take used := by
  by_cases queued : d.pending = 0
  · have resumed : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2 := by
      rcases resume with pending | input | retry | initial
      · exact False.elim (pending queued)
      · exact Or.inl input
      · exact Or.inr (Or.inl retry)
      · exact Or.inr (Or.inr initial)
    exact public_foreign_busy_no_flush_ready_joint_input boundary buffers status level strategy queued pointer output memory wrap inputValid snapshot lower upper resumed encoding checksum
  · obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, written, remaining, _base,
        run, stateA, buffersA, accountA, _sizes, _storage, _outputA, lastA, _count,
        _bits, fields, bytesA, pendingA, wireA,adlerA,_frameA⟩ :=
        public_pending_buffered_exhausted_foreign_adler Z_NO_FLUSH boundary buffers pointer inputValid
          (by decide) (by decide) (by intro impossible; rw [status] at impossible; cases impossible) output enough pending
      have length := public_bytes_length bytesA
      have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
        rw [wireA, wire]
      refine ⟨0, after, z', result, input, origin, base, xs, written, run, stateA,
        buffersA, ?_, ?_, fun _ _ => rfl, ?_, Nat.le_refl _, ?_, Or.inl lastA,
        ⟨remaining, encoded, pendingA, wireAll, meaning⟩,?_,?_⟩
      · rw [length]; exact accountA
      · rw [length]; exact bytesA
      · rw [fields]; rfl
      · rw [fields]; exact status
      · have endA : fillEnd result=fillEnd d := by rw [fields];rfl
        rw [endA]
        exact adlerA.trans checksum
      · rw [fields]
        simp only [List.take_zero,List.append_nil]
        rfl
    · have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
      have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
      have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
      obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, _baseP,
          flushRun, stateM, buffersM, accountM, _sizes, _storage, amountP, _leftP, fieldsM,
          readyM, bytesM, pendingM, wireM,preciseM⟩ :=
        flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
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
      have lastM : dm.last_flush = Z_NO_FLUSH := by rw [fieldsM]
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + producedP) := by
        rw [accountM.2.2.2.2.2.1, pointer]
        rfl
      have wireP : ZlibF.Spec.bytesToBits (published ++ writtenP) ++ remainingP = encoded := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireM ⊢
        rw [wireM, wire]
      have encodingM : RawPrefix middle dm input base (published ++ writtenP) :=
        ⟨remainingP, encoded, pendingM, wireP, meaning⟩
      have validM := input_valid_accounting_output inputValid accountM
      have endM : fillEnd dm=fillEnd d := by rw [fieldsM];rfl
      have adlerM := (flush_pending_low_foreign_run_scalar_effects boundary0.good buffers0 pointer boundary0.bits
        flushRun stateM.good.live.hz accountM).1
      have checksumM : zm.adler=(ZlibF.Spec.adler32 (inputPrefix input (origin+fillEnd dm))).toUInt64 := by
        rw [endM,adlerM];exact checksum
      have snapshot0 := caller_bytes_setD_depth (result:={d with last_flush:=Z_NO_FLUSH}) boundary.good.live.hs rfl snapshot
      have startingBuffers:=buffers0
      obtain ⟨oldZ,oldGet,inputRange,_outRange,separated⟩ := startingBuffers
      have oldEq : oldZ=z := Option.some.inj (oldGet.symm.trans boundary0.good.live.hz)
      subst oldZ
      have separatedP : Separate z.next_in z.avail_in.toNat z.next_out producedP := by
        simpa only [advance_zero] using separate_advance_right (used:=0) separated (by have count:=accountM.2.2.2.1;omega)
      have preciseWide : BufferFrame (setD h ds {d with last_flush:=Z_NO_FLUSH}) middle (fun b=>StreamRoot r b ∨ DeflateOwned ds {d with last_flush:=Z_NO_FLUSH} b)
          [⟨z.next_out,producedP⟩] := by
        refine ⟨full_frame_weaken preciseM.1 ?_,preciseM.2⟩
        intro b changed
        exact changed.elim Or.inl (fun same=>Or.inr (Or.inl same))
      have snapshotKept:=foreign_caller_input_bytes_preserved boundary0.good buffers0 pointer inputRange separatedP
        (Nat.le_refl _) snapshot0 preciseWide (Zlib.Deflate.BorrowProofs.stable_flush_pending _ _ _ _ flushRun)
      have inputM : zm.next_in=z.next_in := by rw [accountM.2.2.2.2.1,advance_zero]
      have availM : zm.avail_in=z.avail_in := UInt32.toNat_inj.mp (by have count:=accountM.2.2.1;omega)
      have snapshotM : Bytes middle zm.next_in zm.avail_in.toNat actualInput := by
        rw [inputM,availM];exact snapshotKept
      obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
          dataRun, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, statusA,
          lastA, encodingA,adlerA,inputLedgerA⟩ :=
        public_foreign_busy_no_flush_data_joint_input stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM outputM) validM snapshotM encodingM checksumM
      have entry := public_pending_no_flush_continue boundary.good stateM.good status
        (by rw [pointer]; intro impossible; cases impossible)
        (by intro zero; rw [zero] at output; contradiction) inputValid queued flushRun
        (by intro zero; rw [zero] at outputM; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases impossible)
      have actual := entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans dataRun)
      obtain ⟨effectUsed, effectProduced, other, otherZ, otherD, effectRun, effectGood,
          effectAccount, _inputEffect, _outputEffect, outputEffect⟩ :=
        public_foreign_busy_slow_no_flush_output_execution stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM outputM) validM
      have effect : ByteOutputInterval middle after (.dstate_depth owner) (oo + producedP) written.length :=
        ByteOutputInterval.identify effectRun dataRun effectGood.live.hz stateA.good.live.hz effectAccount accountA outputEffect
      have lengthP := public_bytes_length bytesM
      have earlier : Bytes after z.next_out producedP writtenP := by
        rw [pointer] at bytesM ⊢
        have effectP : ByteOutputInterval middle after (.dstate_depth owner) (oo + producedP) written.length := effect
        rw [← lengthP] at effectP
        have oldBytes : Bytes middle (.ref (.dstate_depth owner) oo) writtenP.length writtenP := by rw [lengthP]; exact bytesM
        simpa only [lengthP] using effectP.keep_published_bytes oldBytes
      have newBytes : Bytes after (.ref (.dstate_depth owner) (oo + producedP)) written.length written := by
        rw [pointerM] at bytesA
        exact bytesA
      have combinedBytes := generic_published_bytes_append (by simpa only [pointer] using earlier) newBytes
      have account : StreamAccounting z z' used (writtenP ++ written).length := by
        simpa only [List.length_append, lengthP, Nat.zero_add] using stream_accounting_trans accountM accountA
      have agrees : ∀ i, i < origin + fillEnd d → nextInput i = input i := by
        simpa only [endM] using agreesA
      have endpoint : nextOrigin + fillEnd result = origin + fillEnd d + used := by
        simpa only [endM] using endpointA
      rw [lastM] at lastA
      refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, writtenP ++ written,
        actual, stateA, buffersA, account, ?_, agrees, endpoint, baseA, statusA, lastA, ?_,adlerA,?_⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using encodingA
      · simpa only [endM] using inputLedgerA


end Zlib.Deflate.Engine.Proofs
