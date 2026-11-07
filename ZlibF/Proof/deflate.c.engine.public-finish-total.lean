import ZlibF.Proof.«deflate.c.engine.finishing-new-input»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»

/-! # Every ordinary FINISH request retains the initialized protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every default public FINISH request with null or raw output returns
and preserves the initialized protocol. This includes new input after
finishing, output exhaustion before that refusal, zero public output and
invalid input/output pointers. Full counters, heap frame and output-format
refinement remain separate obligations. -/
theorem DefaultFinishBoundary.finish_total {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨err, after, z', allowed, run, stateA, buffersA, accountA⟩ :=
      boundary.entry_refusals Z_FINISH buffers (by decide) (by decide) refused
    exact ⟨0, 0, err, after, z', d, run, stateA, buffersA, accountA, Or.inr (Or.inr allowed)⟩
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null :=
      fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have nonzeroNat : z.avail_out.toNat ≠ 0 := fun eq => nonzero (UInt32.toNat_inj.mp eq)
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    by_cases newInput : d.status = FINISH_STATE ∧ z.avail_in ≠ 0
    · have phase : FinishingPhase d config := by
        rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
        · have impossible := start.status.symm.trans newInput.1
          cases (show INIT_STATE ≠ FINISH_STATE from by decide) impossible
        · obtain ⟨_input, _origin, _base, _xs, _state, status⟩ := working
          have impossible := status.symm.trans newInput.1
          cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible
        · exact finishing
      obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, phaseA, lastA, _inputA, _exhaustedA⟩ :=
        public_default_finishing_new_input boundary.good buffers phase pointer valid newInput.2 output boundary.lower boundary.upper
      have reachableA : StreamReachable .deflate after r := by
        apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) boundary.reachable
        · exact ⟨rfl, rfl⟩
        · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
        · simpa only [Call.execute, heapCall, run]
      have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
        rcases lastA with eq | eq <;> rw [eq] <;> decide
      refine ⟨0, produced, rc, after, z', result, run,
        ⟨goodA, reachableA, boundary.configuration, Or.inr (Or.inr phaseA), bounds.1, bounds.2⟩,
        buffersA, accountA, ?_⟩
      rcases allowed with ok | err
      · exact Or.inl ok
      · exact Or.inr (Or.inr (Or.inr err))
    · have accepted : d.status = FINISH_STATE → z.avail_in = 0 := by
        intro status
        by_cases empty : z.avail_in = 0
        · exact empty
        · exact False.elim (newInput ⟨status, empty⟩)
      obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed, _ended⟩ :=
        boundary.finish buffers pointer output valid accepted
      refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, ?_⟩
      rcases allowed with ok | ended
      · exact Or.inl ok
      · exact Or.inr (Or.inl ended)

end Zlib.Deflate.Engine.Proofs
