import ZlibF.Proof.«deflate.c.engine.common-header-complete-encoding»
import ZlibF.Proof.«deflate.c.engine.common-first-valid-header»
import ZlibF.Proof.«deflate.c.engine.common-data-no-flush-storage»

/-! # Full resource and counter effects for every first common NO_FLUSH capacity -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every accepted first NO_FLUSH call has exact counters, including one or two output bytes. -/
theorem public_common_first_no_flush_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (positive : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
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
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, _outA, _pendingA, statusA, lastA⟩ :=
      first_common_finish_one_buffered initial boundary buffers pointer oneWord valid
    have noFlushRun := first_common_valid_one_source initial trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid Z_NO_FLUSH (by decide) (by decide)
    have same := first_common_finish_one_source initial trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have run : deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) := noFlushRun.trans (same.symm.trans finishRun)
    have heaps : after = levelHeaderOneHeap h r ds pb ob oo z d buf output :=
      (Prod.mk.inj (Except.ok.inj (run.symm.trans noFlushRun))).2
    have expected : r.get (levelHeaderOneHeap h r ds pb ob oo z d buf output) =
        some (pendingStream z (.ref (.blk ob) (oo + 1)) 1) := by
      rw [levelHeaderOneHeap, ZStreamRef.get_setD]
      exact ZStreamRef.get_put_same (by simpa only [levelHeaderOneBytes, stream_get_bytes] using initial.good.live.hz) _
    have streamEq : z' = pendingStream z (.ref (.blk ob) (oo + 1)) 1 := by
      rw [← heaps] at expected
      exact Option.some.inj (stateA.good.live.hz.symm.trans expected)
    have storage : OutputStorage h (levelHeaderOneHeap h r ds pb ob oo z d buf output) r ds pb ob :=
      header_write_storage initial.good trees.base.bytes outGet separate _ _ _ _
    rw [← heaps] at storage
    refine ⟨0, 1, after, z', result, run, stateA.good, accountA, ?_, ?_,
      storage.shape, storage.private_frame trees.base.pbuf, full_shape_live_change storage.shape,
      storage.nalloc, storage.nextBlk⟩
    · rw [streamEq]; simp only [pendingStream]; change z.total_in = z.total_in + 0; rw [UInt64.add_zero]
    · rw [streamEq]; rfl
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_common_header_complete initial trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid
    have contentH := common_header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have stateH : BufferedBoundary (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        common_header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have buffersH := common_header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, after, z', result, run, goodA, accountA, inputA, outputA, shapeA, frameA, _liveA, allocA, nextA⟩ :=
      public_common_slow_no_flush_full_storage_execution stateH buffersH rfl low high initial.strategy pointerH memory wrapConfig readyH valid
    have storageH := common_header_complete_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
    have shape := storageH.shape.trans shapeA
    have frame := full_frame_trans_shape (storageH.private_frame trees.base.pbuf) frameA storageH.shape
    have effectsH := header_complete_stream_counter_effects z ob oo
    refine ⟨used, 2 + produced, after, z', result, first.trans run, goodA, ?_, ?_, ?_, shape, frame, full_shape_live_change shape,
        allocA.trans storageH.nalloc, nextA.trans storageH.nextBlk⟩
    · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
    · rw [inputA, effectsH.1]
    · rw [outputA, effectsH.2, UInt64.ofNat_add, UInt64.add_assoc]


end Zlib.Deflate.Engine.Proofs
