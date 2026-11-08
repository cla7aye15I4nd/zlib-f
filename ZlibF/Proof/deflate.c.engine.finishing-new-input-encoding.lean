import ZlibF.Proof.«deflate.c.engine.encoded-state-refusals»
import ZlibF.Proof.«deflate.c.engine.finishing-new-input»

/-! # Finished streams retain encoding when new input is refused -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- New input after the final block is not consumed. The actual call may
first publish pending output, including an exhausted-output OK return,
before it can reach BUF_ERROR. Both paths retain the exact completed
encoding and checksum on their actual final heap. -/
theorem public_finishing_new_input_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (encoding : FinishedEncoding h d accepted published) :
    ∃ rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 written.length ∧
      Bytes after z.next_out written.length written ∧ FinishingPhase result config ∧
      FinishedEncoding after result accepted (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧ (rc = Z_OK ∨ rc = Z_BUF_ERROR) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; cases output
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  have encoding0 := encoding.last_flush good Z_FINISH
  by_cases queued : d.pending = 0
  · have source := public_finished_new_input_source good phase.status queued nonnull positive (valid nonempty) nonempty lower upper
    obtain ⟨message, refused⟩ := err_return_run good0.live.hz Z_BUF_ERROR
    let z' := { z with msg := message }
    have goodA := stream_control_good (z' := z') good0 rfl good.live.zalloc good.live.zfree
    have accountA : StreamAccounting z z' 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers good0 goodA buffers0 accountA
    refine ⟨Z_BUF_ERROR, _, z', _, [], source.trans refused, goodA, buffersA, accountA,
      caller_output_zero_slice (z := z') goodA buffersA, phase0, ?_, checksum, Or.inr rfl⟩
    simpa only [List.append_nil] using encoding0.put_stream r z'
  · obtain ⟨_pb, produced, middle, zm, dm, written, _base, flushRun, goodM, buffersM,
        accountM, _storage, amount, _pendingCount, fields, reset, bytesM, encodingM, adlerM⟩ :=
      flush_pending_finished_encoding good0 buffers0 pointer encoding0
    have moved : 0 < produced := by
      rw [amount]
      apply Nat.lt_min.mpr
      refine ⟨?_, output⟩
      have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      change 0 < d.pending.toNat
      omega
    have phaseM : FinishingPhase dm config := by
      apply phase0.control (by rw [fields])
      intro _ emptyM
      exact reset moved (by rw [emptyM]; rfl)
    have inputM : zm.avail_in = z.avail_in := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      omega
    have checksumM : zm.adler = (ZlibF.Spec.adler32 accepted).toUInt64 := adlerM.trans checksum
    have length := caller_bytes_length bytesM
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive valid queued flushRun exhausted
      have phaseA : FinishingPhase { dm with last_flush := -1 } config :=
        phaseM.control rfl (fun w p => phaseM.cursor w p)
      have bytesA := caller_bytes_setD_depth (result := {dm with last_flush := -1}) goodM.live.hs rfl bytesM
      refine ⟨Z_OK, _, zm, _, written, run, last_flush_good goodM (-1),
        last_flush_buffers goodM buffersM (-1), ?_, ?_, phaseA, encodingM.last_flush goodM (-1), checksumM, Or.inl rfl⟩
      · rw [length]; exact accountM
      · rw [length]; exact bytesA
    · have newInput : zm.avail_in ≠ 0 := by rw [inputM]; exact nonempty
      have source := public_pending_finish_new_input_source good goodM nonnull positive valid queued flushRun exhausted phaseM.status newInput
      obtain ⟨message, refused⟩ := err_return_run goodM.live.hz Z_BUF_ERROR
      let z' := { zm with msg := message }
      have goodA := stream_control_good (z' := z') goodM rfl goodM.live.zalloc goodM.live.zfree
      have accountA : StreamAccounting zm z' 0 0 := stream_accounting_zero zm
      have buffersA := stream_control_buffers goodM goodA buffersM accountA
      have finalAccount : StreamAccounting z z' 0 written.length := by
        rw [length]
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountM accountA
      have bytesA : Bytes (r.put middle z') z.next_out produced written := by
        rcases bytesM with null | ⟨ref, offset, array, pointer, get, bound, slice⟩
        · exact Or.inl null
        · exact Or.inr ⟨ref, offset, array, pointer, (byte_get_stream_put middle r z' ref).trans get, bound, slice⟩
      refine ⟨Z_BUF_ERROR, _, z', dm, written, source.trans refused, goodA, buffersA, finalAccount,
        ?_, phaseM, encodingM.put_stream r z', checksumM, Or.inr rfl⟩
      rw [length]; exact bytesA

end Zlib.Deflate.Engine.Proofs
