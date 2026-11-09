import ZlibF.Proof.«deflate.c.engine.common-header-finish-boundary»
import ZlibF.Proof.«deflate.c.engine.common-header-complete-encoding»
import ZlibF.Proof.«deflate.c.engine.common-first-no-flush-storage»
import ZlibF.Proof.«deflate.c.engine.common-data-finish-storage»

/-! # Full resources for every first common-level FINISH capacity -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real first FINISH call composes a complete header with all data output. -/
theorem public_common_first_finish_fits_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used (2 + produced) ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat (2 + produced) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_common_valid_header_complete initial trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound outputRoom valid Z_FINISH (by decide) (by decide)
  change deflate (some r) Z_FINISH h = publicDataTail (some r) (some (.tab ds)) Z_FINISH
    (levelHeaderFinishHeap h r ds pb ob oo z d buf output) at first
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, by rw [initial.bits]; decide⟩
  obtain ⟨stateH, endH, publishH⟩ := common_header_finish_strategy_boundary boundary frontier publish
    trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (common_header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (common_header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_FINISH
  have accountH := header_complete_accounting pointer outputRoom
  have wrapConfig : config.wrap = 1 :=
    (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  obtain ⟨used, produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
    public_common_slow_data_finish_full_storage stateH endH buffersH rfl low high initial.strategy pointerH memory wrapConfig publishH valid
  have headerStorage := common_header_complete_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
  have goodH := common_header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate
  obtain ⟨shapeH, frameH, _liveH, allocH, nextH⟩ := full_storage_state_trans headerStorage.shape
    (headerStorage.private_frame trees.base.pbuf) headerStorage.nalloc headerStorage.nextBlk goodH.live.hs
    (Or.inr (Or.inl (Or.inl rfl))) { headerCompleteState d with last_flush := Z_FINISH }
  have shape := shapeH.trans shapeA
  have frame := full_frame_trans_shape frameH frameA shapeH
  have effectsH := header_complete_stream_counter_effects z ob oo
  refine ⟨used, produced, rc, after, z', result, first.trans run, goodA, ?_, ?_, ?_, shape, frame, full_shape_live_change shape,
      allocA.trans allocH, nextA.trans nextH⟩
  · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  · rw [inputA, effectsH.1]
  · rw [outputA, effectsH.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Every positive raw capacity on the first FINISH call has exact totals.
Header splits and exactly two output bytes use their actual source paths. -/
theorem public_common_first_finish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨used, produced, after, z', result, run, goodA, accountA, inputA, outputA, storage⟩ :=
      public_common_first_no_flush_full_storage_execution initial low high boundary buffers pointer output memory valid
    have actual := (first_common_valid_one_eq_finish initial buffers pointer oneWord valid Z_NO_FLUSH
      (by decide) (by decide)).symm.trans run
    exact ⟨used, produced, Z_OK, after, z', result, actual, goodA, accountA, inputA, outputA, storage⟩
  · have ready : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, storage⟩ :=
      public_common_first_finish_fits_full_storage_execution initial low high (boundary.strategy ready) boundary.end_frontier
        buffers pointer (by omega) memory valid
    exact ⟨used, 2 + produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, storage⟩

end Zlib.Deflate.Engine.Proofs
