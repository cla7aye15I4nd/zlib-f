import ZlibF.Proof.«deflate.c.engine.public-no-flush-total»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-protocol»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-duplicate»

/-! # Every signed-input common-level NO_FLUSH request preserves the phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Includes pointer refusals, zero output, all input sizes, empty retries,
duplicates and requests made after finishing; raw or null output is explicit. -/
theorem CommonSlowFinishBoundary.no_flush_total {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (rc, after) ∧
      CommonSlowFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
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
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
    · obtain ⟨used, produced, after, z', result, run, stateA, buffersA, accountA, _statusA⟩ :=
        boundary.no_flush_resuming buffers pointer output valid (fun _ => resume) unfinished
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
        rcases boundary.phase with working | finishing
        · obtain ⟨_input, _origin, _base, _xs, _state, status⟩ := working
          exact status
        · exact False.elim (unfinished finishing.status)
      obtain ⟨after, z', run, stateA, buffersA, accountA⟩ :=
        boundary.duplicate_no_flush buffers status input pending nonnull nonzero lower
      exact ⟨0, 0, Z_BUF_ERROR, after, z', _, run, stateA, buffersA, accountA, Or.inr (Or.inr rfl)⟩


end Zlib.Deflate.Engine.Proofs
