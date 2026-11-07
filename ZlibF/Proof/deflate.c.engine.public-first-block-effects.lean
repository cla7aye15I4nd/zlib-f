import ZlibF.Proof.«deflate.c.engine.public-first-block»
import ZlibF.Proof.«deflate.c.engine.public-first-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-first-full-storage»

/-! # Exact counters and memory effects of the actual initial BLOCK call -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual complete BLOCK header and data path retain exact counters,
caller output interval and full storage/allocation frame, including exactly
two output bytes and the resulting zero-capacity strategy call. -/
theorem public_first_block_fits_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      deflate (some r) Z_BLOCK h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used (2 + produced) ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat (2 + produced) ∧
      RawOutputInterval h after ob oo (2 + produced) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨caller, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have low := trees.base.lit_lo; omega
  have first := public_default_valid_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound outputRoom valid Z_BLOCK (by decide) (by decide)
  have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
  have baseH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf caller) r ds
      (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
    ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
      boundary.bits, boundary.strict, header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
      fun _ => initial.pendingOut⟩
  have stateH := last_flush_buffered_boundary baseH Z_BLOCK
  have buffersH := last_flush_buffers baseH.good
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_BLOCK
  have accountH := header_complete_accounting pointer outputRoom
  have wrapConfig : config.wrap = 1 :=
    (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have publishH : PublishReady { headerCompleteState d with last_flush := Z_BLOCK } :=
    ⟨initial.pending, initial.pendingOut, boundary.bits⟩
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  obtain ⟨used, produced, after, z', result, run, goodA, _buffersA, accountA,
      inputA, outputA, intervalA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
    public_busy_slow_block_effect_execution (stateH.strategy publishH) stateH.end_frontier buffersH
      rfl level initial.strategy pointerH memory wrapConfig publishH valid
  have headerStorage := header_complete_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
  have goodH := header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate
  obtain ⟨shapeH, frameH, _liveH, allocH, nextH⟩ := full_storage_state_trans headerStorage.shape
    (headerStorage.private_frame trees.base.pbuf) headerStorage.nalloc headerStorage.nextBlk goodH.live.hs
    (Or.inr (Or.inl (Or.inl rfl))) { headerCompleteState d with last_flush := Z_BLOCK }
  have headerEffect : RawOutputInterval h (headerCompleteHeap h r ds pb ob oo z d buf caller) ob oo 2 :=
    header_complete_output_effect outGet (by omega)
  have storeEffect : RawOutputInterval (headerCompleteHeap h r ds pb ob oo z d buf caller)
      (setD (headerCompleteHeap h r ds pb ob oo z d buf caller) ds
        { headerCompleteState d with last_flush := Z_BLOCK }) ob (oo + 2) 0 := .of_same rfl
  have beforeData : RawOutputInterval h
      (setD (headerCompleteHeap h r ds pb ob oo z d buf caller) ds
        { headerCompleteState d with last_flush := Z_BLOCK }) ob oo 2 := by
    simpa only [Nat.add_zero] using headerEffect.trans storeEffect
  have interval := beforeData.trans intervalA
  have shape := shapeH.trans shapeA
  have effectsH := header_complete_stream_counter_effects z ob oo
  refine ⟨used, produced, after, z', result, first.trans run, goodA, ?_, ?_, ?_, interval,
    shape, full_frame_trans_shape frameH frameA shapeH, full_shape_live_change shape,
    allocA.trans allocH, nextA.trans nextH⟩
  · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  · rw [inputA, effectsH.1]
  · rw [outputA, effectsH.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Every positive-capacity initial default BLOCK call has the same exact
effects, including the one-byte header split before any strategy call. -/
theorem public_first_block_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      deflate (some r) Z_BLOCK h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨caller, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
    obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
    have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
    subst oldD
    have separate : ob ≠ pb := by
      intro same
      subst ob
      exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    have room : 2 ≤ buf.size := by have size := trees.base.size; have low := trees.base.lit_lo; omega
    obtain ⟨after, z', result, finishRun, stateA, _buffersA, accountA, _rest⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have blockSource := first_valid_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid Z_BLOCK (by decide) (by decide)
    have finishSource := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have run := blockSource.trans (finishSource.symm.trans finishRun)
    have totals := first_ordinary_one_run_counter_effects (Or.inr rfl) initial level buffers pointer oneWord valid
      finishRun stateA.good.live.hz accountA
    have interval := first_ordinary_one_run_output_effect (Or.inr rfl) initial level buffers pointer oneWord valid
      finishRun stateA.good.live.hz accountA
    have storage := first_ordinary_one_run_full_storage (Or.inr rfl) initial level buffers pointer oneWord valid finishRun
    exact ⟨0, 1, after, z', result, run, stateA.good, accountA, totals.1, totals.2, interval, storage⟩
  · obtain ⟨used, produced, after, z', result, run, goodA, accountA, inputA, outputA, interval, storage⟩ :=
      public_first_block_fits_effect_execution initial level boundary buffers pointer (by omega) memory valid
    exact ⟨used, 2 + produced, after, z', result, run, goodA, accountA, inputA, outputA, interval, storage⟩

end Zlib.Deflate.Engine.Proofs
