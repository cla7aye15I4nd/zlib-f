import ZlibF.Proof.«deflate.c.engine.public-busy-full-storage»
import ZlibF.Proof.«deflate.c.engine.refusal-counters»

/-! # Complete heap frames for actual public refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual static error lookup and message store change only the stream record. -/
theorem err_return_run_full_storage {h after : Heap} {r : ZStreamRef}
    {z : ZStream} {err rc : Int32}
    (live : r.get h = some z) (run : ERR_RETURN (some r) err h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (StreamRoot r) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨message, expected⟩ := err_return_run live err
  have same := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
  rw [← same]
  have shape := shape_put live { z with msg := message }
  exact ⟨shape, stream_store_full_frame h r _, full_shape_live_change shape, by simp, by simp⟩

/-- Every actual legal-flag entry refusal retains all objects outside the stream record. -/
theorem DefaultFinishBoundary.entry_refusal_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (StreamRoot r) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases streamBad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · have source := public_stream_guard_refusal boundary.good flush flagLo flagHi streamBad
    exact err_return_run_full_storage boundary.good.live.hz (source.symm.trans run)
  · have out : z.next_out ≠ .null := fun eq => streamBad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => streamBad (Or.inr (Or.inl ⟨count, eq⟩))
    have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
      intro status
      by_cases flag : flush = Z_FINISH
      · exact flag
      · exact False.elim (streamBad (Or.inr (Or.inr ⟨status, flag⟩)))
    have empty : z.avail_out = 0 := by
      rcases refused with bad | bad | bad | empty
      · exact False.elim (out bad)
      · exact False.elim (valid bad.1 bad.2)
      · exact False.elim (bad.2 (finish bad.1))
      · exact empty
    have source := public_zero_output_refusal boundary.good flush flagLo flagHi out valid finish empty
    exact err_return_run_full_storage boundary.good.live.hz (source.symm.trans run)

/-- Duplicate NO_FLUSH requests change only the stream record and private state slot. -/
theorem public_duplicate_no_flush_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {rc : Int32}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE)
    (input : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : 0 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ b = ds) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have source := public_busy_no_flush_duplicate_source good status input pending out positive lower upper
  have get : r.get (setD h ds { d with last_flush := Z_NO_FLUSH }) = some z := by
    simpa only [ZStreamRef.get_setD] using good.live.hz
  obtain ⟨shapeA, frameA, _liveA, allocA, nextA⟩ := err_return_run_full_storage get (source.symm.trans run)
  have shape0 := shape_setD good.live.hs { d with last_flush := Z_NO_FLUSH }
  have frame0 := full_frame_weaken (state_store_full_frame h ds { d with last_flush := Z_NO_FLUSH })
    (fun _ same => Or.inr same : ∀ b, b = ds → StreamRoot r b ∨ b = ds)
  have shape := shape0.trans shapeA
  have frame := full_frame_trans_shape frame0 (full_frame_weaken frameA (fun _ root => Or.inl root)) shape0
  exact ⟨shape, frame, full_shape_live_change shape, allocA, nextA⟩

end Zlib.Deflate.Engine.Proofs
