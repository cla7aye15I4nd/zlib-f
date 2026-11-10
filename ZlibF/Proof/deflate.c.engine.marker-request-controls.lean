import ZlibF.Proof.«deflate.c.engine.marker-request-total»

/-! # The actual STREAM_ERROR guard for every initialized marker request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual initialized PARTIAL/SYNC/FULL request returns STREAM_ERROR exactly
for its public pointer or FINISH_STATE guard. Duplicate/no-output BUF_ERROR
and every real compression/pending return remain distinct. -/
theorem DefaultFinishBoundary.marker_run_controls {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    (rc = Z_STREAM_ERROR ↔ z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl | rfl <;> decide
  have nonfinal : flush ≠ Z_FINISH := by rcases flag with rfl | rfl | rfl <;> decide
  by_cases bad : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · have guard : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) := by
      rcases bad with output | input | finish
      · exact Or.inl output
      · exact Or.inr (Or.inl ⟨input.2, input.1⟩)
      · exact Or.inr (Or.inr finish)
    have source := public_stream_guard_refusal boundary.good flush flagLo flagHi guard
    obtain ⟨message, refused⟩ := err_return_run boundary.good.live.hz Z_STREAM_ERROR
    have value : Z_STREAM_ERROR = rc := (Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))).1
    exact ⟨fun _ => bad, fun _ => value.symm⟩
  · have nonnull : z.next_out ≠ .null := fun eq => bad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => bad (Or.inr (Or.inl ⟨eq, count⟩))
    have active : d.status ≠ FINISH_STATE := fun status => bad (Or.inr (Or.inr ⟨status, nonfinal⟩))
    have notError : rc ≠ Z_STREAM_ERROR := by
      by_cases empty : z.avail_out = 0
      · have source := public_zero_output_refusal boundary.good flush flagLo flagHi nonnull valid
          (fun status => False.elim (active status)) empty
        obtain ⟨message, refused⟩ := err_return_run boundary.good.live.hz Z_BUF_ERROR
        have value : Z_BUF_ERROR = rc := (Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))).1
        rw [← value]
        decide
      · have output : 0 < z.avail_out.toNat := by
          have value : z.avail_out.toNat ≠ 0 := fun eq => empty (UInt32.toNat_inj.mp eq)
          omega
        obtain ⟨ob, oo, pointer⟩ := raw.resolve_left nonnull
        obtain ⟨used, produced, computed, other, z', result, tested, _stateA, _buffersA, _accountA, allowed⟩ :=
          boundary.marker_active buffers pointer output valid active flush flag
        have value : computed = rc := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).1
        rw [value] at allowed
        intro error
        rcases allowed with ok | buf
        · exact (show Z_OK ≠ Z_STREAM_ERROR from by decide) (ok.symm.trans error)
        · exact (show Z_BUF_ERROR ≠ Z_STREAM_ERROR from by decide) (buf.symm.trans error)
    exact ⟨fun error => False.elim (notError error), fun guard => False.elim (bad guard)⟩

end Zlib.Deflate.Engine.Proofs
