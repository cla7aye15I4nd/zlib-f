import ZlibF.Proof.«deflate.c.engine.finish-new-input-source»
import ZlibF.Proof.«deflate.c.engine.stream-control»
import ZlibF.Proof.«deflate.c.engine.finishing-phase»

/-! # Pending publication precedes the finished-state new-input refusal -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- New input after FINISH_STATE is either left for a later refusal
while old pending bytes exhaust output, or refused after their actual
drain. The one-time trailer is never repeated. -/
theorem public_default_finishing_new_input {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR) ∧ FinishingPhase result config ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧ z'.avail_in = z.avail_in ∧
      (rc = Z_OK → z'.avail_out = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  by_cases queued : d.pending = 0
  · have source := public_finished_new_input_source good phase.status queued nonnull positive (valid nonempty) nonempty lower upper
    obtain ⟨message, refused⟩ := err_return_run good0.live.hz Z_BUF_ERROR
    let z' := { z with msg := message }
    have goodA := stream_control_good (z' := z') good0 rfl good.live.zalloc good.live.zfree
    have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers good0 goodA buffers0 account
    refine ⟨0, Z_BUF_ERROR, _, z', _, source.trans refused, goodA, buffersA, account, Or.inr rfl,
      phase0, Or.inr rfl, rfl, ?_⟩
    intro impossible
    cases (show Z_BUF_ERROR ≠ Z_OK from by decide) impossible
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, _pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM⟩ :=
      flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
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
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive valid queued flushRun exhausted
      have phaseF : FinishingPhase { dm with last_flush := -1 } config :=
        phaseM.control rfl (fun w p => phaseM.cursor w p)
      exact ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1),
        last_flush_buffers goodM buffersM (-1), accountM, Or.inl rfl, phaseF, Or.inl rfl, inputM, fun _ => exhausted⟩
    · have newInput : zm.avail_in ≠ 0 := by rw [inputM]; exact nonempty
      have source := public_pending_finish_new_input_source good goodM nonnull positive valid queued flushRun exhausted phaseM.status newInput
      obtain ⟨message, refused⟩ := err_return_run goodM.live.hz Z_BUF_ERROR
      let z' := { zm with msg := message }
      have goodA := stream_control_good (z' := z') goodM rfl goodM.live.zalloc goodM.live.zfree
      have account : StreamAccounting zm z' 0 0 := stream_accounting_zero zm
      have buffersA := stream_control_buffers goodM goodA buffersM account
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      refine ⟨produced, Z_BUF_ERROR, _, z', dm, source.trans refused, goodA, buffersA, ?_, Or.inr rfl,
        phaseM, Or.inr lastM, inputM, ?_⟩
      · simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountM account
      · intro impossible
        cases (show Z_BUF_ERROR ≠ Z_OK from by decide) impossible

end Zlib.Deflate.Engine.Proofs
