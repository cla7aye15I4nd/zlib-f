import ZlibF.Proof.«deflate.c.engine.public-pending-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»

/-! # Precise public caller-buffer frames for actual ordinary requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Finishing-state new-input requests preserve the pending interval before their actual refusal. -/
theorem public_finishing_new_input_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  have enterEffect : RawOutputInterval h (setD h ds { d with last_flush := Z_FINISH }) ob oo 0 := .of_same rfl
  by_cases queued : d.pending = 0
  · have source := public_finished_new_input_source good phase.status queued nonnull positive (valid nonempty) nonempty lower upper
    obtain ⟨message, refused⟩ := err_return_run good0.live.hz Z_BUF_ERROR
    let z' := { z with msg := message }
    have goodA := stream_control_good (z' := z') good0 rfl good.live.zalloc good.live.zfree
    have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers good0 goodA buffers0 account
    refine ⟨0, Z_BUF_ERROR, _, z', _, source.trans refused, goodA, account, rfl, by simp [z'], ?_⟩
    have errorStorage := err_return_run_full_storage good0.live.hz refused
    have privateFrame := full_frame_weaken errorStorage.2.1 (fun _ root => Or.inl root : ∀ b, StreamRoot r b → StreamRoot r b ∨ DeflateOwned ds { d with last_flush := Z_FINISH } b)
    have errorEffect : RawOutputInterval (setD h ds { d with last_flush := Z_FINISH }) _ ob oo 0 :=
      .of_private_frame good0 buffers0 pointer privateFrame
    simpa only [Nat.zero_add] using enterEffect.trans errorEffect
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, _pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM⟩ :=
      flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
    have effectsM := flush_pending_low_run_counter_effects good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have pendingEffect := flush_pending_low_run_output_effect good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have beforeReturn : RawOutputInterval h middle ob oo produced := by
      simpa only [Nat.zero_add] using enterEffect.trans pendingEffect
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
      refine ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1), accountM, effectsM.1, effectsM.2, ?_⟩
      have returnEffect : RawOutputInterval middle (setD middle ds { dm with last_flush := -1 }) ob (oo + produced) 0 := .of_same rfl
      simpa only [Nat.add_zero] using beforeReturn.trans returnEffect
    · have newInput : zm.avail_in ≠ 0 := by rw [inputM]; exact nonempty
      have source := public_pending_finish_new_input_source good goodM nonnull positive valid queued flushRun exhausted phaseM.status newInput
      obtain ⟨message, refused⟩ := err_return_run goodM.live.hz Z_BUF_ERROR
      let z' := { zm with msg := message }
      have goodA := stream_control_good (z' := z') goodM rfl goodM.live.zalloc goodM.live.zfree
      have account : StreamAccounting zm z' 0 0 := stream_accounting_zero zm
      have buffersA := stream_control_buffers goodM goodA buffersM account
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      have errorStorage := err_return_run_full_storage goodM.live.hz refused
      have privateFrame := full_frame_weaken errorStorage.2.1
        (fun _ root => Or.inl root : ∀ b, StreamRoot r b → StreamRoot r b ∨ DeflateOwned ds dm b)
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      have errorEffect : RawOutputInterval middle _ ob (oo + produced) 0 :=
        .of_private_frame goodM buffersM pointerM privateFrame
      have interval : RawOutputInterval h (r.put middle z') ob oo produced := by
        simpa only [Nat.add_zero] using beforeReturn.trans errorEffect
      refine ⟨produced, Z_BUF_ERROR, _, z', dm, source.trans refused, goodA, ?_, effectsM.1, effectsM.2, interval⟩
      simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountM account

/-- After the final block, only the actual one-time trailer can write caller output. -/
theorem public_finishing_tail_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0) (pending : d.pending = 0) :
    ∃ produced rc after z' result,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other, pb, buf, trees⟩ := good.trees
    have eq : other = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨produced, after, z', result, run, goodA, account, inputA, outputA, interval⟩ :=
      zlib_trailer_output_execution good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have header := public_finishing_header_source good phase empty
    exact ⟨produced, if result.pending != 0 then Z_OK else Z_STREAM_END, after, z', result,
      header.trans run, goodA, account, inputA, outputA, interval⟩
  · exact ⟨0, Z_STREAM_END, h, z, d,
      public_finished_headers good phase.status empty phase.lookahead wrap,
      good, stream_accounting_zero z, rfl, by simp, RawOutputInterval.of_same rfl⟩

/-- Every accepted finishing-phase call composes existing pending output and the one-time trailer interval. -/
theorem public_finishing_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  have enterEffect : RawOutputInterval h (setD h ds { d with last_flush := Z_FINISH }) ob oo 0 := .of_same rfl
  by_cases queued : d.pending = 0
  · obtain ⟨produced, rc, after, z', result, tailRun, goodA, account, inputA, outputA, intervalA⟩ :=
      public_finishing_tail_output_execution good0 buffers0 phase0 pointer empty queued
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    exact ⟨produced, rc, after, z', result, entry.trans (source.symm.trans tailRun), goodA, account, inputA, outputA,
      (by simpa only [Nat.zero_add] using enterEffect.trans intervalA)⟩
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, _pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM⟩ :=
      flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
    have effectsM := flush_pending_low_run_counter_effects good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have pendingEffect := flush_pending_low_run_output_effect good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have beforeReturn : RawOutputInterval h middle ob oo produced := by
      simpa only [Nat.zero_add] using enterEffect.trans pendingEffect
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
      refine ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1), accountM, effectsM.1, effectsM.2, ?_⟩
      have returnEffect : RawOutputInterval middle (setD middle ds { dm with last_flush := -1 }) ob (oo + produced) 0 := .of_same rfl
      simpa only [Nat.add_zero] using beforeReturn.trans returnEffect
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
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨laterProduced, rc, after, z', result, tailRun, goodA, accountA, inputA, outputA, intervalA⟩ :=
        public_finishing_tail_output_execution goodM buffersM phaseM pointerM emptyM noPending
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun exhausted (fun _ => emptyM)
      refine ⟨produced + laterProduced, rc, after, z', result, entry.trans tailRun, goodA,
        ?_, inputA.trans effectsM.1, ?_, beforeReturn.trans intervalA⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]

end Zlib.Deflate.Engine.Proofs
