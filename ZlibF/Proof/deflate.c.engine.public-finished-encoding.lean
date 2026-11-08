import ZlibF.Proof.«deflate.c.engine.finishing-tail-encoding»
import ZlibF.Proof.«deflate.c.engine.finishing-output-interval»

/-! # Actual finishing calls retain complete independent stream encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every accepted actual FINISH call after the final block retains the
complete encoding, with exact output on its final heap. Pending block and
trailer bytes may span any number of positive-capacity calls and legal
caller replacements. Empty input is the accepted finishing protocol; new
input and wrong-flush refusals are separate source branches. STREAM_END
gives independent zlib validity for the accumulated actual output. -/
theorem public_default_finishing_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (encoding : FinishedEncoding h d accepted published) :
    ∃ rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 written.length ∧
      Bytes after z.next_out written.length written ∧ FinishingPhase result config ∧
      FinishedEncoding after result accepted (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written)) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  have encoding0 := encoding.last_flush good Z_FINISH
  by_cases queued : d.pending = 0
  · obtain ⟨rc, after, z', result, written, tailRun, goodA, buffersA, accountA,
        bytesA, phaseA, encodingA, _wrapA, checksumA, endedA⟩ :=
      public_finishing_tail_encoding good0 buffers0 phase0 pointer empty queued checksum encoding0
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    exact ⟨rc, after, z', result, written, entry.trans (source.symm.trans tailRun), goodA, buffersA,
      accountA, bytesA, phaseA, encodingA, checksumA, endedA⟩
  · obtain ⟨_pb, producedP, middle, zm, dm, writtenP, _baseP, flushRun, goodM, buffersM,
        accountM, _storageM, amountP, pendingCount, fieldsM, resetM, bytesM, encodingM, adlerM⟩ :=
      flush_pending_finished_encoding good0 buffers0 pointer encoding0
    have moved : 0 < producedP := by
      rw [amountP]
      apply Nat.lt_min.mpr
      refine ⟨?_, output⟩
      have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      change 0 < d.pending.toNat
      omega
    have phaseM : FinishingPhase dm config := by
      apply phase0.control (by rw [fieldsM])
      intro _ emptyM
      exact resetM moved (by rw [emptyM]; rfl)
    have emptyM : zm.avail_in = 0 := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      rw [empty] at count
      exact count
    have checksumM : zm.adler = (ZlibF.Spec.adler32 accepted).toUInt64 := adlerM.trans checksum
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive (by simp [empty]) queued flushRun exhausted
      have phaseF : FinishingPhase { dm with last_flush := -1 } config :=
        phaseM.control rfl (fun w p => phaseM.cursor w p)
      have encodingF := encodingM.last_flush goodM (-1)
      have bytesF := caller_bytes_setD_depth (result := { dm with last_flush := -1 }) goodM.live.hs rfl bytesM
      have lengthP := caller_bytes_length bytesM
      refine ⟨Z_OK, _, zm, _, writtenP, run, last_flush_good goodM (-1),
        last_flush_buffers goodM buffersM (-1), ?_, ?_, phaseF, encodingF, checksumM, ?_⟩
      · rw [lengthP]; exact accountM
      · rw [lengthP]; exact bytesF
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · have noPending : dm.pending = 0 := by
        apply UInt64.toNat_inj.mp
        change dm.pending.toNat = 0
        have balance := accountM.2.2.2.1
        change producedP = min d.pending.toNat z.avail_out.toNat at amountP
        change dm.pending.toNat + producedP = d.pending.toNat at pendingCount
        have nonzero : zm.avail_out.toNat ≠ 0 := fun zero => exhausted (UInt32.toNat_inj.mp zero)
        omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + producedP) := by
        rw [accountM.2.2.2.2.2.1, pointer]
        rfl
      obtain ⟨rc, after, z', result, written, tailRun, goodA, buffersA, accountA,
          bytesA, phaseA, encodingA, _wrapA, checksumA, endedA⟩ :=
        public_finishing_tail_encoding goodM buffersM phaseM pointerM emptyM noPending checksumM encodingM
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued
        flushRun exhausted (fun _ => emptyM)
      obtain ⟨_effectProduced, _effectRc, _other, _otherZ, _otherD, effectRun, effectGood,
          effectAccount, _effectInput, _effectOutput, outputEffect⟩ :=
        public_finishing_tail_output_execution goodM buffersM phaseM pointerM emptyM noPending
      have effect : RawOutputInterval middle after ob (oo + producedP) written.length :=
        RawOutputInterval.identify effectRun tailRun effectGood.live.hz goodA.live.hz effectAccount accountA outputEffect
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
      have account : StreamAccounting z z' 0 (writtenP ++ written).length := by
        simpa only [List.length_append, lengthP, Nat.zero_add] using stream_accounting_trans accountM accountA
      refine ⟨rc, after, z', result, writtenP ++ written, entry.trans tailRun, goodA, buffersA,
        account, ?_, phaseA, ?_, checksumA, ?_⟩
      · simpa only [List.length_append, lengthP, pointer] using combinedBytes
      · simpa only [List.append_assoc] using encodingA
      · intro ended
        simpa only [List.append_assoc] using endedA ended

end Zlib.Deflate.Engine.Proofs
