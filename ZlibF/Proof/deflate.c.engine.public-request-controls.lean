import ZlibF.Proof.«deflate.c.engine.public-request-buffer-frame»

/-! # Scoped default public safety and control contracts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual ordinary requests return STREAM_ERROR exactly at their entry
guards, and STREAM_END has the public final-state conditions. Both facts
follow from actual calls and live returned records. -/
theorem DefaultFinishBoundary.ordinary_run_controls {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z returned : ZStream} {d result : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after))
    (live : r.get after = some returned) (state : after.dstates ds = some result) :
    (rc = Z_STREAM_ERROR ↔ z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
      returned.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) := by
  have bounds : 0 ≤ flush.toInt ∧ flush.toInt ≤ Z_BLOCK.toInt := by
    rcases flag with rfl | rfl <;> decide
  by_cases bad : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · have sourceBad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) := by simpa only [and_comm] using bad
    have source := public_stream_guard_refusal boundary.good flush bounds.1 bounds.2 sourceBad
    obtain ⟨_message, refused⟩ := err_return_run boundary.good.live.hz Z_STREAM_ERROR
    have code : Z_STREAM_ERROR = rc := (Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))).1
    refine ⟨⟨fun _ => bad, fun _ => code.symm⟩, ?_⟩
    intro ended
    have impossible : Z_STREAM_ERROR = Z_STREAM_END := code.trans ended
    cases (show Z_STREAM_ERROR ≠ Z_STREAM_END from by decide) impossible
  · have noError (neq : rc ≠ Z_STREAM_ERROR) :
        rc = Z_STREAM_ERROR ↔ z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
          (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
      ⟨fun yes => False.elim (neq yes), fun yes => False.elim (bad yes)⟩
    have nonnull : z.next_out ≠ .null := fun eq => bad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => bad (Or.inr (Or.inl ⟨eq, count⟩))
    have finishAllowed : d.status = FINISH_STATE → flush = Z_FINISH := by
      intro finished
      by_cases yes : flush = Z_FINISH
      · exact yes
      · exact False.elim (bad (Or.inr (Or.inr ⟨finished, yes⟩)))
    by_cases zero : z.avail_out = 0
    · have source := public_zero_output_refusal boundary.good flush bounds.1 bounds.2 nonnull valid finishAllowed zero
      obtain ⟨_message, refused⟩ := err_return_run boundary.good.live.hz Z_BUF_ERROR
      have code : Z_BUF_ERROR = rc := (Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))).1
      refine ⟨noError (by rw [← code]; decide), ?_⟩
      intro ended
      cases (show Z_BUF_ERROR ≠ Z_STREAM_END from by decide) (code.trans ended)
    · have positive : 0 < z.avail_out.toNat := by
        have nonzero : z.avail_out.toNat ≠ 0 := fun eq => zero (UInt32.toNat_inj.mp eq)
        omega
      obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
      rcases flag with rfl | rfl
      · have unfinished : d.status ≠ FINISH_STATE := by
          intro finished
          cases (show Z_NO_FLUSH ≠ Z_FINISH from by decide) (finishAllowed finished)
        by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
        · obtain ⟨_read, _written, computed, _ze, _de, tested, _stateA, _buffersA, _accountA, _statusA⟩ :=
            boundary.no_flush_resuming buffers pointer positive valid (fun _ => resume) unfinished
          have code : Z_OK = rc := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).1
          refine ⟨noError (by rw [← code]; decide), ?_⟩
          intro ended
          cases (show Z_OK ≠ Z_STREAM_END from by decide) (code.trans ended)
        · have pending : d.pending = 0 := by
            by_cases yes : d.pending = 0
            · exact yes
            · exact False.elim (resume (Or.inl yes))
          have input : z.avail_in = 0 := by
            by_cases yes : z.avail_in = 0
            · exact yes
            · exact False.elim (resume (Or.inr (Or.inl yes)))
          have lower : 0 ≤ d.last_flush.toInt := by
            have lo := boundary.lower
            have notRetry : d.last_flush.toInt ≠ -1 := fun eq => resume (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp eq))))
            have notInitial : d.last_flush.toInt ≠ -2 := fun eq => resume (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp eq))))
            omega
          have status : d.status = BUSY_STATE := by
            rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
            · exact False.elim (resume (Or.inr (Or.inr (Or.inr start.lastFlush))))
            · obtain ⟨_input, _origin, _base, _xs, _state, status⟩ := working
              exact status
            · exact False.elim (unfinished finishing.status)
          obtain ⟨_computed, _ze, tested, _stateA, _buffersA, _accountA⟩ :=
            boundary.duplicate_no_flush buffers status input pending nonnull zero lower
          have code : Z_BUF_ERROR = rc := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).1
          refine ⟨noError (by rw [← code]; decide), ?_⟩
          intro ended
          cases (show Z_BUF_ERROR ≠ Z_STREAM_END from by decide) (code.trans ended)
      · by_cases newInput : d.status = FINISH_STATE ∧ z.avail_in ≠ 0
        · have phase : FinishingPhase d config := by
            rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
            · cases (show INIT_STATE ≠ FINISH_STATE from by decide) (start.status.symm.trans newInput.1)
            · obtain ⟨_input, _origin, _base, _xs, _state, status⟩ := working
              cases (show BUSY_STATE ≠ FINISH_STATE from by decide) (status.symm.trans newInput.1)
            · exact finishing
          obtain ⟨_written, computed, _heap, _ze, _de, tested, _goodA, _buffersA, _accountA,
              allowed, _phaseA, _lastA, _inputA, _exhaustedA⟩ :=
            public_default_finishing_new_input boundary.good buffers phase pointer valid newInput.2 positive boundary.lower boundary.upper
          have code : computed = rc := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).1
          rw [code] at allowed
          have neq : rc ≠ Z_STREAM_ERROR := by rcases allowed with rfl | rfl <;> decide
          have notEnd : rc ≠ Z_STREAM_END := by rcases allowed with rfl | rfl <;> decide
          exact ⟨noError neq, fun ended => False.elim (notEnd ended)⟩
        · have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
            intro finished
            by_cases empty : z.avail_in = 0
            · exact empty
            · exact False.elim (newInput ⟨finished, empty⟩)
          obtain ⟨_read, _written, computed, _heap, ze, de, tested, stateA, _buffersA, _accountA, allowed, ended⟩ :=
            boundary.finish buffers pointer positive valid accepted
          have same := Prod.mk.inj (Except.ok.inj (tested.symm.trans run))
          have sameZ := actual_run_stream_unique tested run stateA.good.live.hz live
          have getD := stateA.good.live.hs
          rw [same.2] at getD
          have sameD : de = result := Option.some.inj (getD.symm.trans state)
          rw [same.1] at allowed
          rw [same.1, sameZ, sameD] at ended
          have neq : rc ≠ Z_STREAM_ERROR := by rcases allowed with rfl | rfl <;> decide
          refine ⟨noError neq, ?_⟩
          intro done
          have final := ended done
          exact ⟨rfl, final.1, final.2.2.1, final.2.2.2.2.1, Int32.toInt_inj.mp final.2.2.2.2.2⟩

end Zlib.Deflate.Engine.Proofs
