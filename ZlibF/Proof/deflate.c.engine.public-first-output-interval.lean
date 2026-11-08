import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # Precise public caller-buffer frames for actual ordinary requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both real ordinary first calls with one output byte preserve the exact one-byte header interval. -/
theorem first_ordinary_one_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {flush rc : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (initial : EngineStart h r ds z d) (level : d.level = 6) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have actual : deflate (some r) flush h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
    rcases flag with rfl | rfl
    · exact first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
    · exact first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
  have get : r.get (headerOneHeap h r ds pb ob oo z d buf output) =
      some (pendingStream z (.ref (.blk ob) (oo + 1)) 1) := by
    unfold headerOneHeap
    rw [ZStreamRef.get_setD]
    apply ZStreamRef.get_put_same
    simpa only [headerOneBytes, stream_get_bytes] using initial.good.live.hz
  have expected := pending_stream_accounting (z := z) 1 pointer (by rw [one]; decide)
  have effect : RawOutputInterval h (headerOneHeap h r ds pb ob oo z d buf output) ob oo 1 :=
    header_one_output_effect outGet (by simpa only [one, show ((1 : UInt32).toNat) = 1 from rfl] using outBound)
  exact RawOutputInterval.identify actual run get live expected account effect

/-- The actual first FINISH call composes the complete header with its entire data/trailer interval. -/
theorem public_first_finish_fits_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used (2 + produced) ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat (2 + produced) ∧ RawOutputInterval h after ob oo (2 + produced) := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have first := public_default_finish_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound outputRoom valid
  have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, by rw [initial.bits]; decide⟩
  obtain ⟨stateH, endH, publishH⟩ := header_finish_strategy_boundary boundary frontier publish
    trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_FINISH
  have accountH := header_complete_accounting pointer outputRoom
  have wrapConfig : config.wrap = 1 :=
    (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  obtain ⟨used, produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, intervalA⟩ :=
    public_busy_slow_finish_output_execution stateH endH buffersH rfl level initial.strategy pointerH memory wrapConfig publishH valid
  have headerEffect : RawOutputInterval h (headerCompleteHeap h r ds pb ob oo z d buf output) ob oo 2 :=
    header_complete_output_effect outGet (by omega)
  have statusEffect : RawOutputInterval (headerCompleteHeap h r ds pb ob oo z d buf output)
      (setD (headerCompleteHeap h r ds pb ob oo z d buf output) ds
        { headerCompleteState d with last_flush := Z_FINISH }) ob (oo + 2) 0 := .of_same rfl
  have beforeData : RawOutputInterval h
      (setD (headerCompleteHeap h r ds pb ob oo z d buf output) ds
        { headerCompleteState d with last_flush := Z_FINISH }) ob oo 2 := by
    simpa only [Nat.add_zero] using headerEffect.trans statusEffect
  have interval := beforeData.trans intervalA
  have effectsH := header_complete_stream_counter_effects z ob oo
  refine ⟨used, produced, rc, after, z', result, first.trans run, goodA, ?_, ?_, ?_, interval⟩
  · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
  · rw [inputA, effectsH.1]
  · rw [outputA, effectsH.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Every accepted actual first NO_FLUSH call has its exact output interval, including split headers. -/
theorem public_first_no_flush_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (positive : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
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
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have noFlushRun := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have same := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have run : deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) := noFlushRun.trans (same.symm.trans finishRun)
    have effects := first_ordinary_one_run_counter_effects (Or.inl rfl) initial level buffers pointer oneWord valid
      run stateA.good.live.hz accountA
    exact ⟨0, 1, after, z', result, run, stateA.good, accountA, effects.1, effects.2,
      first_ordinary_one_run_output_effect (Or.inl rfl) initial level buffers pointer oneWord valid run stateA.good.live.hz accountA⟩
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid
    have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have stateH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have buffersH := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, after, z', result, run, goodA, accountA, inputA, outputA, intervalA⟩ :=
      public_busy_slow_no_flush_output_execution stateH buffersH rfl level initial.strategy pointerH memory wrapConfig readyH valid
    have headerEffect : RawOutputInterval h (headerCompleteHeap h r ds pb ob oo z d buf output) ob oo 2 :=
      header_complete_output_effect outGet (by omega)
    have interval := headerEffect.trans intervalA
    have effectsH := header_complete_stream_counter_effects z ob oo
    refine ⟨used, 2 + produced, after, z', result, first.trans run, goodA, ?_, ?_, ?_, interval⟩
    · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
    · rw [inputA, effectsH.1]
    · rw [outputA, effectsH.2, UInt64.ofNat_add, UInt64.add_assoc]

/-- Every positive raw capacity on the real first FINISH call has its exact accounted output interval. -/
theorem public_first_finish_output_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced := by
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, run, stateA, _buffersA, accountA, _rest⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have effects := first_ordinary_one_run_counter_effects (Or.inr rfl) initial level buffers pointer oneWord valid
      run stateA.good.live.hz accountA
    exact ⟨0, 1, Z_OK, after, z', result, run, stateA.good, accountA, effects.1, effects.2,
      first_ordinary_one_run_output_effect (Or.inr rfl) initial level buffers pointer oneWord valid run stateA.good.live.hz accountA⟩
  · have ready : PublishReady d := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, intervalA⟩ :=
      public_first_finish_fits_output_execution initial level (boundary.strategy ready) boundary.end_frontier
        buffers pointer (by omega) memory valid
    exact ⟨used, 2 + produced, rc, after, z', result, run, goodA, accountA, inputA, outputA, intervalA⟩

end Zlib.Deflate.Engine.Proofs
