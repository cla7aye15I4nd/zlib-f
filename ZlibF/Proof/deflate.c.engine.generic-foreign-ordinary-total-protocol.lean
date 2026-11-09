import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-accepted-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-phase»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-total»
import ZlibF.Proof.«deflate.c.engine.public-finish-total»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every default public NO_FLUSH request with null or foreign depth output returns
and preserves the initialized protocol. Includes parameter/zero-output
refusals, all input lengths, empty retries, duplicate requests and calls
made after finishing. Full counters, heap frame and format refinement are
separate obligations. -/
theorem DefaultFinishBoundary.foreign_no_flush_total {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_NO_FLUSH ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨err, after, z', allowed, run, stateA, buffersA, accountA⟩ :=
      boundary.entry_refusals Z_NO_FLUSH buffers (by decide) (by decide) refused
    exact ⟨0, 0, err, after, z', d, run, stateA, buffersA, accountA, Or.inr allowed⟩
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null :=
      fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have unfinished : d.status ≠ FINISH_STATE :=
      fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq, by decide⟩)))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have nonzeroNat : z.avail_out.toNat ≠ 0 := fun eq => nonzero (UInt32.toNat_inj.mp eq)
      omega
    by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
    · obtain ⟨used, produced, after, z', result, run, stateA, buffersA, accountA, _statusA⟩ :=
        boundary.foreign_no_flush_resuming buffers pointer output valid (fun _ => resume) unfinished
      exact ⟨used, produced, Z_OK, after, z', result, run, stateA, buffersA, accountA, Or.inl rfl⟩
    · have pending : d.pending = 0 := by
        by_cases zero : d.pending = 0
        · exact zero
        · exact False.elim (resume (Or.inl zero))
      have input : z.avail_in = 0 := by
        by_cases zero : z.avail_in = 0
        · exact zero
        · exact False.elim (resume (Or.inr (Or.inl zero)))
      have lower : 0 ≤ d.last_flush.toInt := by
        have low := boundary.lower
        have notRetry : d.last_flush.toInt ≠ -1 := fun eq =>
          resume (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp eq))))
        have notInitial : d.last_flush.toInt ≠ -2 := fun eq =>
          resume (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp eq))))
        omega
      have status : d.status = BUSY_STATE := by
        rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
        · exact False.elim (resume (Or.inr (Or.inr (Or.inr start.lastFlush))))
        · obtain ⟨_input, _origin, _base, _xs, _state, status⟩ := working
          exact status
        · exact False.elim (unfinished finishing.status)
      obtain ⟨after, z', run, stateA, buffersA, accountA⟩ :=
        boundary.duplicate_no_flush buffers status input pending nonnull nonzero lower
      exact ⟨0, 0, Z_BUF_ERROR, after, z', _, run, stateA, buffersA, accountA, Or.inr (Or.inr rfl)⟩

/-- Every default public FINISH request with null or foreign depth output returns
and preserves the initialized protocol. This includes new input after
finishing, output exhaustion before that refusal, zero public output and
invalid input/output pointers. Full counters, heap frame and output-format
refinement remain separate obligations. -/
theorem DefaultFinishBoundary.foreign_finish_total {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) :
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
        public_default_foreign_finishing_new_input boundary.good buffers phase pointer valid newInput.2 output boundary.lower boundary.upper
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
        boundary.foreign_finish buffers pointer output valid accepted
      refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, ?_⟩
      rcases allowed with ok | ended
      · exact Or.inl ok
      · exact Or.inr (Or.inl ended)


end Zlib.Deflate.Engine.Proofs
