import ZlibF.Proof.«deflate.c.engine.block-protocol»

/-! # The exact STREAM_ERROR guard of an initialized BLOCK request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual initialized BLOCK request returns STREAM_ERROR exactly
for its public pointer or FINISH_STATE guard. Duplicate/no-output BUF_ERROR
and every real compression/pending return remain distinct. -/
theorem DefaultFinishBoundary.block_run_controls {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_BLOCK h = .ok (rc, after)) :
    (rc = Z_STREAM_ERROR ↔ z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ Z_BLOCK ≠ Z_FINISH)) := by
  by_cases bad : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨
      (d.status = FINISH_STATE ∧ Z_BLOCK ≠ Z_FINISH)
  · have guard : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ Z_BLOCK ≠ Z_FINISH) := by
      rcases bad with output | input | finish
      · exact Or.inl output
      · exact Or.inr (Or.inl ⟨input.2, input.1⟩)
      · exact Or.inr (Or.inr finish)
    have source := public_stream_guard_refusal boundary.good Z_BLOCK (by decide) (by decide) guard
    obtain ⟨message, refused⟩ := err_return_run boundary.good.live.hz Z_STREAM_ERROR
    have value : Z_STREAM_ERROR = rc := (Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))).1
    exact ⟨fun _ => bad, fun _ => value.symm⟩
  · have nonnull : z.next_out ≠ .null := fun eq => bad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => bad (Or.inr (Or.inl ⟨eq, count⟩))
    have active : d.status ≠ FINISH_STATE := fun status => bad (Or.inr (Or.inr ⟨status, by decide⟩))
    have notError : rc ≠ Z_STREAM_ERROR := by
      by_cases empty : z.avail_out = 0
      · have source := public_zero_output_refusal boundary.good Z_BLOCK (by decide) (by decide) nonnull valid
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
          boundary.block_active buffers pointer output valid active
        have value : computed = rc := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).1
        rw [value] at allowed
        intro error
        rcases allowed with ok | buf
        · exact (show Z_OK ≠ Z_STREAM_ERROR from by decide) (ok.symm.trans error)
        · exact (show Z_BUF_ERROR ≠ Z_STREAM_ERROR from by decide) (buf.symm.trans error)
    exact ⟨fun error => False.elim (notError error), fun guard => False.elim (bad guard)⟩

end Zlib.Deflate.Engine.Proofs
