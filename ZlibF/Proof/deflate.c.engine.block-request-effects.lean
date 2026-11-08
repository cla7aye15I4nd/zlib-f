import ZlibF.Proof.«deflate.c.engine.public-busy-block-effects»
import ZlibF.Proof.«deflate.c.engine.public-first-block-effects»
import ZlibF.Proof.«deflate.c.engine.refusal-output-interval»

/-! # Exact effects of every actual initialized BLOCK request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every legal NULL-output refusal has zero actual input/output movement.
The result follows from the executed refusal, not from total-counter wrap. -/
theorem DefaultFinishBoundary.legal_null_output_run_counts {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (low : 0 ≤ flush.toInt) (high : flush.toInt ≤ Z_BLOCK.toInt) (pointer : z.next_out = .null)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some z')
    (account : StreamAccounting z z' used produced) : used = 0 ∧ produced = 0 := by
  obtain ⟨err, other, returned, _allowed, tested, stateA, _buffersA, known⟩ :=
    boundary.entry_refusals flush buffers low high (Or.inl pointer)
  have same := actual_run_stream_unique tested run stateA.good.live.hz live
  rw [same] at known
  exact stream_accounting_counts_unique account known

/-- Every actual initialized BLOCK run with raw output has exact totals,
the accounted output interval, full object frame and no allocation changes.
Entry refusals, first headers, pending-first returns and duplicates are
included. Its execution and preservation theorem supplies the run premise. -/
theorem DefaultFinishBoundary.block_raw_run_effects {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_BLOCK h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧ returned.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_BLOCK ≠ Z_FINISH) ∨ z.avail_out = 0
  · have totals := boundary.entry_refusal_run_counter_effects (by decide) (by decide) refused run live account
    have interval := boundary.entry_refusal_run_output_effect (produced := produced) buffers pointer (by decide) (by decide) refused run
    obtain ⟨shape, frame, liveA, alloc, next⟩ := boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run
    exact ⟨totals.1, totals.2, interval, shape,
      full_frame_weaken frame (fun _ root => Or.inl root), liveA, alloc, next⟩
  · have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have value : z.avail_out.toNat ≠ 0 := fun eq => nonzero (UInt32.toNat_inj.mp eq)
      omega
    have active : d.status ≠ FINISH_STATE := fun status => refused (Or.inr (Or.inr (Or.inl ⟨status, by decide⟩)))
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨accepted, delivered, other, otherZ, otherD, tested, goodA, accountA,
          inputA, outputA, intervalA, shapeA, frameA, liveA, allocA, nextA⟩ :=
        public_first_block_effect_execution start level state buffers pointer output boundary.configuration.memory valid
      have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      have streams := actual_run_stream_unique tested run goodA.live.hz live
      have totals := stream_counter_effects_identify streams accountA account inputA outputA
      have interval := RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
      refine ⟨totals.1, totals.2, interval, ?_⟩
      rw [← heaps]
      exact ⟨shapeA, frameA, liveA, allocA, nextA⟩
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨accepted, delivered, computed, other, otherZ, otherD, tested, goodA, accountA,
          inputA, outputA, intervalA, shapeA, frameA, liveA, allocA, nextA⟩ :=
        public_busy_block_effect_execution state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      have streams := actual_run_stream_unique tested run goodA.live.hz live
      have totals := stream_counter_effects_identify streams accountA account inputA outputA
      have interval := RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
      refine ⟨totals.1, totals.2, interval, ?_⟩
      rw [← heaps]
      exact ⟨shapeA, frameA, liveA, allocA, nextA⟩
    · exact False.elim (active finishing.status)

end Zlib.Deflate.Engine.Proofs
