import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-resume»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-tail-phase»
import ZlibF.Proof.«deflate.c.engine.public-finishing-phase»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every positive-capacity actual FINISH call in the finishing phase,
with no new input, preserves that phase. It may finish queued block bytes,
append its single trailer, drain a queued trailer or return STREAM_END
without another write. This is the accepted protocol, not full output refinement. -/
theorem public_default_foreign_finishing_phase {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ FinishingPhase result config ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧ z'.avail_in = 0 ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  by_cases queued : d.pending = 0
  · obtain ⟨produced, rc, after, z', result, tailRun, goodA, buffersA, account, allowed, phaseA, last, emptyA, ended⟩ :=
      public_foreign_finishing_tail_phase good0 buffers0 phase0 pointer empty queued
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    exact ⟨produced, rc, after, z', result, entry.trans (source.symm.trans tailRun), goodA, buffersA,
      account, allowed, phaseA, Or.inr last, emptyA, ended⟩
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, _pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM,_fullFrame⟩ :=
      flush_pending_resume_foreign_bits good0 buffers0 pointer low pending0
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
    have emptyM : zm.avail_in = 0 := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      rw [empty] at count
      exact count
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive (by simp [empty]) queued flushRun exhausted
      have phaseF : FinishingPhase { dm with last_flush := -1 } config :=
        phaseM.control rfl (fun w p => phaseM.cursor w p)
      refine ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1),
        last_flush_buffers goodM buffersM (-1), accountM, Or.inl rfl, phaseF, Or.inl rfl, emptyM, ?_⟩
      intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · have left : 0 < zm.avail_out.toNat := by
        have nonzero : zm.avail_out.toNat ≠ 0 := fun zero => exhausted (UInt32.toNat_inj.mp zero)
        omega
      have noPending : dm.pending = 0 := by
        apply UInt64.toNat_inj.mp
        change dm.pending.toNat = 0
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        change dm.pending.toNat + produced = d.pending.toNat at _pendingCount
        omega
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨laterProduced, rc, after, z', result, tailRun, goodA, buffersA, accountA, allowed, phaseA, last, emptyA, ended⟩ :=
        public_foreign_finishing_tail_phase goodM buffersM phaseM pointerM emptyM noPending
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun exhausted (fun _ => emptyM)
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      rw [lastM] at last
      refine ⟨produced + laterProduced, rc, after, z', result, entry.trans tailRun, goodA, buffersA,
        ?_, allowed, phaseA, Or.inr last, emptyA, ended⟩
      simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA


end Zlib.Deflate.Engine.Proofs
