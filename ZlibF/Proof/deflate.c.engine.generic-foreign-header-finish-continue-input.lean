import ZlibF.Proof.«deflate.c.borrow-stable-publish»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-data-completed»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-data-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-pending-one»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.public-header-finish-continue-encoding»

/-! # Actual split-header FINISH resumption enters complete encoded compression -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- With room beyond the remaining default header byte, actual FINISH
resumption emits 156 then performs complete compression and trailer
publication. The logical accepted input is exactly the consumed original
caller snapshot. No raw encoding seed is assumed: draining the actual
header establishes the empty raw phase. -/
theorem public_foreign_header_finish_continue_encoding {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (room : 1 < z.avail_out.toNat)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 []).toUInt64) (encoding : HeaderPending h d [120]) :
    ∃ used rc after z' result rawWritten accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase rawWritten ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ FinishedEncoding after result accepted rawWritten)) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ rawWritten)) := by
  have shape := encoding.one_remaining
  have headerEncoding := encoding
  obtain ⟨_held, _pendingBytes, _headerEq, headerBits, headerStart, headerLook⟩ := headerEncoding
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  have pending0 := last_flush_pending_bits boundary.good shape.2 Z_FINISH
  obtain ⟨_pb, producedP, middle, zm, dm, writtenP, remainingP, baseP,
      flushRun, stateM, buffersM, accountM, _sizes, storageM, amountP, leftP, fieldsM,
      readyM, bytesM, pendingM, wireM,preciseM⟩ :=
    flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
  have countP : producedP = 1 := by
    change producedP = min d.pending.toNat z.avail_out.toNat at amountP
    rw [shape.1, Nat.min_eq_left (by omega)] at amountP
    exact amountP
  have emptyM : dm.pending.toNat = 0 := by
    change dm.pending.toNat + producedP = d.pending.toNat at leftP
    rw [shape.1, countP] at leftP
    omega
  have bitsM : dm.bi_valid.toInt.toNat = 0 := by rw [fieldsM]; exact headerBits
  obtain ⟨writtenEq, encodingM⟩ := header_byte_drain_encoding (input := input) pendingM emptyM bitsM wireM
  have outputM : 0 < zm.avail_out.toNat := by
    have count := accountM.2.2.2.1
    rw [countP] at count
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fieldsM]; exact status
  have levelM : dm.level = 6 := by rw [fieldsM]; exact level
  have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact strategy
  have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + producedP) := by
    rw [accountM.2.2.2.2.2.1, pointer]
    rfl
  have validM := input_valid_accounting_output valid accountM
  have adlerM := (flush_pending_low_foreign_run_scalar_effects boundary0.good buffers0 pointer boundary0.bits
    flushRun stateM.good.live.hz accountM).1
  have endM : fillEnd dm = fillEnd d := by rw [fieldsM]; rfl
  have prefixEmpty : inputPrefix input (0 + fillEnd dm) = [] := by
    rw [endM]
    simp only [fillEnd, headerStart, headerLook, UInt32.toNat_zero, Nat.add_zero,
      inputPrefix, List.range_zero, List.map_nil]
  have checksumM : zm.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd dm))).toUInt64 := by
    rw [prefixEmpty, adlerM]
    exact checksum
  have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_FINISH }) boundary.good.live.hs rfl snapshot
  have snapshotM : Bytes middle zm.next_in zm.avail_in.toNat actualInput := by
    have originalBuffers := buffers0
    obtain ⟨oldZ,oldGet,inputRange,_outputRange,separated⟩ := originalBuffers
    have oldEq : oldZ=z := Option.some.inj (oldGet.symm.trans boundary0.good.live.hz)
    subst oldZ
    have separateNow : Separate z.next_in z.avail_in.toNat z.next_out producedP := by
      simpa only [advance_zero] using separate_advance_right (used:=0) separated (show 0+producedP≤z.avail_out.toNat by rw [countP];omega)
    have preciseWide : BufferFrame (setD h ds {d with last_flush:=Z_FINISH}) middle
        (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,producedP⟩] :=
      ⟨full_frame_weaken preciseM.1 (fun _ yes => yes.elim Or.inl (fun same => Or.inr (Or.inl same))),preciseM.2⟩
    have kept := foreign_caller_input_bytes_preserved boundary0.good buffers0 pointer inputRange separateNow
      (Nat.le_refl _) snapshot0 preciseWide (Zlib.Deflate.BorrowProofs.stable_flush_pending _ _ _ _ flushRun)
    have inputPointer : zm.next_in=z.next_in := by simpa only [advance_zero] using accountM.2.2.2.2.1
    have inputCount : zm.avail_in=z.avail_in := UInt32.toNat_inj.mp (by have count:=accountM.2.2.1;omega)
    rw [inputPointer,inputCount]
    exact kept
  obtain ⟨used, rc, after, z', result, rawWritten, accepted, acceptedA, dataRun, goodA, buffersA,
      accountA, bytesA, checksumA, phasesA, endedA⟩ :=
    public_foreign_busy_finish_data_completed_encoding stateM buffersM statusM levelM strategyM pointerM memory wrap
      (readyM outputM) validM snapshotM checksumM encodingM
  have acceptedEq : accepted = actualInput.take used := by simpa only [prefixEmpty, List.nil_append] using acceptedA
  have queued : d.pending ≠ 0 := by intro zero; rw [zero] at shape; simp at shape
  have entry := public_pending_finish_continue boundary.good stateM.good
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at room; contradiction) valid queued flushRun
    (by intro zero; rw [zero] at outputM; contradiction)
    (by intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
  have actual := entry.trans ((public_busy_header_skip stateM.good statusM).trans dataRun)
  have effect := public_foreign_busy_finish_data_run_output_interval stateM buffersM statusM levelM strategyM pointerM
    memory wrap (readyM outputM) validM dataRun goodA.live.hz accountA
  have earlier : Bytes after (.ref (.dstate_depth owner) oo) 1 [156] := by
    have oldBytes : Bytes middle (.ref (.dstate_depth owner) oo) [156].length [156] := by
      simpa only [pointer, countP, writtenEq, List.length_cons, List.length_nil] using bytesM
    have kept : ByteOutputInterval middle after (.dstate_depth owner) (oo + [156].length) rawWritten.length := by
      simpa only [List.length_cons, List.length_nil, countP] using effect
    exact kept.keep_published_bytes oldBytes
  have current : Bytes after (.ref (.dstate_depth owner) (oo + 1)) rawWritten.length rawWritten := by
    simpa only [pointerM, countP] using bytesA
  have combinedBytes := generic_published_bytes_append earlier current
  have account : StreamAccounting z z' used (1 + rawWritten.length) := by
    simpa only [countP, Nat.zero_add] using stream_accounting_trans accountM accountA
  refine ⟨used, rc, after, z', result, rawWritten, accepted, acceptedEq, actual, goodA, buffersA,
    account, ?_, checksumA, ?_, ?_⟩
  · simpa only [List.length_cons, List.length_nil, pointer] using combinedBytes
  · simpa only [List.nil_append] using phasesA
  · intro ended
    simpa only [List.append_nil] using endedA ended

end Zlib.Deflate.Engine.Proofs
