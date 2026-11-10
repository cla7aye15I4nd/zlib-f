import ZlibF.Proof.«deflate.c.engine.public-finishing-phase»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Four caller bytes complete the actual one-time trailer after the raw
pending suffix is drained. A negative wrapper needs no extra publication. -/
theorem public_finishing_tail_budget {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0) (pending : d.pending = 0)
    (room : 4 ≤ z.avail_out.toNat) :
    ∃ produced after z' result,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (Z_STREAM_END, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced := by
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other, pb, buf, trees⟩ := good.trees
    have same : other = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, account,
        _sizes, _storage, amount, left, _wrapA, _bitsA, _fields, _bytes, _pendingA, _output⟩ :=
      zlib_trailer_publish good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have producedFour : produced = 4 := amount.trans (Nat.min_eq_left room)
    have pendingZero : result.pending = 0 := UInt64.toNat_inj.mp (by
      change result.pending.toNat = 0
      omega)
    have source := public_finishing_header_source good phase empty
    rw [pendingZero] at run
    exact ⟨produced, after, z', result, source.trans run, goodA, buffersA, account⟩
  · exact ⟨0, h, z, d, public_finished_headers good phase.status empty phase.lookahead wrap,
      good, buffers, stream_accounting_zero z⟩

/-- A finishing call with no new input completes when caller space covers
the real queued suffix and four possible trailer bytes. This direct
publication budget is a phase lemma, not the public deflateBound theorem. -/
theorem public_finishing_pending_budget {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (room : d.pending.toNat + 4 ≤ z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_STREAM_END, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at room; change d.pending.toNat + 4 ≤ 0 at room; omega
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  by_cases queued : d.pending = 0
  · obtain ⟨produced, after, z', result, run, goodA, buffersA, account⟩ :=
      public_finishing_tail_budget good0 buffers0 phase0 pointer empty queued (by omega)
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    exact ⟨produced, after, z', result, entry.trans (source.symm.trans run), goodA, buffersA, account⟩
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM⟩ :=
      flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
    change produced = min d.pending.toNat z.avail_out.toNat at amount
    have producedAll : produced = d.pending.toNat := amount.trans (Nat.min_eq_left (by omega))
    have moved : 0 < produced := by
      have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      omega
    have phaseM : FinishingPhase dm config := by
      apply phase0.control (by rw [fields])
      intro _ emptyM
      exact reset moved (by rw [emptyM]; rfl)
    have emptyM : zm.avail_in = 0 := UInt32.toNat_inj.mp (by
      have count := accountM.2.2.1
      simpa only [empty, UInt32.toNat_zero, Nat.add_zero] using count)
    have noPending : dm.pending = 0 := UInt64.toNat_inj.mp (by
      change dm.pending.toNat = 0
      change dm.pending.toNat + produced = d.pending.toNat at pendingCount
      omega)
    have roomM : 4 ≤ zm.avail_out.toNat := by
      have count := accountM.2.2.2.1
      omega
    have nonemptyM : zm.avail_out ≠ 0 := by intro zero; rw [zero] at roomM; change 4 ≤ 0 at roomM; omega
    have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]; rfl
    obtain ⟨later, after, z', result, tailRun, goodA, buffersA, accountA⟩ :=
      public_finishing_tail_budget goodM buffersM phaseM pointerM emptyM noPending roomM
    have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun nonemptyM (fun _ => emptyM)
    refine ⟨produced + later, after, z', result, entry.trans tailRun, goodA, buffersA, ?_⟩
    simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA

end Zlib.Deflate.Engine.Proofs
