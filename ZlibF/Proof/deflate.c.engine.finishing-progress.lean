import ZlibF.Proof.«deflate.c.engine.public-finishing-phase»
import ZlibF.Proof.«deflate.c.engine.counter-effects»

/-! # Finishing publication decreases a finite byte count -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual trailer publication consumes exactly its remaining bytes.
Every unfinished positive-capacity call emits at least one byte. This
uses the real trailer and pending output, without deflateBound. -/
theorem public_finishing_tail_progress {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (pending : d.pending = 0) (output : 0 < z.avail_out.toNat) :
    ∃ produced rc after z' result,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ FinishingPhase result config ∧
      result.last_flush = d.last_flush ∧ z'.avail_in = 0 ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) ∧
      result.pending.toNat + (if result.wrap = 1 then 4 else 0) + produced =
        (if d.wrap = 1 then 4 else 0) ∧
      (rc = Z_OK → 0 < produced) := by
  obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, account,
      allowed, phaseA, last, emptyA, ended⟩ :=
    public_finishing_tail_phase good buffers phase pointer empty pending
  refine ⟨produced, rc, after, z', result, run, goodA, buffersA, account,
    allowed, phaseA, last, emptyA, ended, ?_⟩
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other, pb, buf, trees⟩ := good.trees
    have same : other = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨producedT, afterT, zT, resultT, _written, _remaining, actual, goodT, _buffersT,
        accountT, _sizes, _storage, amount, balance, wrapT, _bitsT, _fields, _bytes, _pendingT, _wire⟩ :=
      zlib_trailer_publish good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have sameRun := Prod.mk.inj (Except.ok.inj
      (((public_finishing_header_source good phase empty).trans actual).symm.trans run))
    have heaps : afterT = after := sameRun.2
    subst afterT
    have streams : zT = z' := Option.some.inj (goodT.live.hz.symm.trans goodA.live.hz)
    have states : resultT = result := Option.some.inj (goodT.live.hs.symm.trans goodA.live.hs)
    subst zT resultT
    have counts := (stream_accounting_counts_unique accountT account).2
    have amountA : produced = min 4 z.avail_out.toNat := counts.symm.trans amount
    have balanceA : result.pending.toNat + produced = 4 := by omega
    have negative : result.wrap ≠ 1 := by rw [wrapT]; decide
    refine ⟨?_, fun _ => ?_⟩
    · simpa only [wrap, if_true, if_neg negative, Nat.add_zero] using balanceA
    · rw [amountA]
      exact Nat.lt_min.mpr ⟨by decide, output⟩
  · have actual := public_finished_headers good phase.status empty phase.lookahead wrap
    have sameRun := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
    have heaps : h = after := sameRun.2
    subst after
    have states : d = result := Option.some.inj (good.live.hs.symm.trans goodA.live.hs)
    subst result
    have streams : z = z' := Option.some.inj (good.live.hz.symm.trans goodA.live.hz)
    subst z'
    have counts := (stream_accounting_counts_unique (stream_accounting_zero z) account).2
    have negative : d.wrap ≠ 1 := by rw [wrap]; decide
    refine ⟨by simp only [pending, UInt64.toNat_zero, if_neg negative]; omega, ?_⟩
    intro ok
    have code : Z_STREAM_END = Z_OK := sameRun.1.trans ok
    exact False.elim ((by decide : Z_STREAM_END ≠ Z_OK) code)

/-- The complete real FINISH call conserves remaining pending and trailer
bytes. With positive caller capacity each unfinished call strictly
reduces that finite total. No global compressed-size estimate is used. -/
theorem public_finishing_publication_progress {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ FinishingPhase result config ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧ z'.avail_in = 0 ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) ∧
      result.pending.toNat + (if result.wrap = 1 then 4 else 0) + produced =
        d.pending.toNat + (if d.wrap = 1 then 4 else 0) ∧
      (rc = Z_OK → 0 < produced) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  by_cases queued : d.pending = 0
  · obtain ⟨produced, rc, after, z', result, tailRun, goodA, buffersA, account, allowed, phaseA, last, emptyA, ended, balance, progress⟩ :=
      public_finishing_tail_progress good0 buffers0 phase0 pointer empty queued output
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    refine ⟨produced, rc, after, z', result, entry.trans (source.symm.trans tailRun), goodA, buffersA,
      account, allowed, phaseA, Or.inr last, emptyA, ended, ?_, progress⟩
    simpa only [queued, UInt64.toNat_zero, Nat.zero_add] using balance
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
        last_flush_buffers goodM buffersM (-1), accountM, Or.inl rfl, phaseF, Or.inl rfl, emptyM, ?_, ?_, ?_⟩
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
      · have sameWrap : dm.wrap = d.wrap := by rw [fields]
        change dm.pending.toNat + produced = d.pending.toNat at _pendingCount
        change dm.pending.toNat + (if dm.wrap = 1 then 4 else 0) + produced = _
        rw [sameWrap]
        omega
      · exact fun _ => moved
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
      obtain ⟨laterProduced, rc, after, z', result, tailRun, goodA, buffersA, accountA, allowed, phaseA, last, emptyA, ended, balance, progress⟩ :=
        public_finishing_tail_progress goodM buffersM phaseM pointerM emptyM noPending left
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun exhausted (fun _ => emptyM)
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      rw [lastM] at last
      refine ⟨produced + laterProduced, rc, after, z', result, entry.trans tailRun, goodA, buffersA,
        ?_, allowed, phaseA, Or.inr last, emptyA, ended, ?_, fun _ => by omega⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · have sameWrap : dm.wrap = d.wrap := by rw [fields]
        rw [sameWrap] at balance
        change dm.pending.toNat + produced = d.pending.toNat at _pendingCount
        rw [noPending] at _pendingCount
        change 0 + produced = d.pending.toNat at _pendingCount
        omega


end Zlib.Deflate.Engine.Proofs
