import ZlibF.Proof.«deflate.c.engine.public-request-controls»

/-! # Scoped default public safety and control contracts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The public call's safety, accounting, precise frame, refusal and terminal
clauses hold for the initialized default ordinary protocol. The explicit
scope is level 6, memory level 8, the zlib wrapper, NO_FLUSH/FINISH and
null/raw-array output. This does not replace the all-operation Goal.deflate. -/
theorem DefaultFinishBoundary.ordinary_request_contract {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, accountA, bytesA,
      inputA, outputA, shapeA, frameA, liveA, allocA, nextA, allowed⟩ := boundary.request_with_buffer_frame flush flag buffers raw
  have controls := boundary.ordinary_run_controls flag buffers raw run stateA.good.live.hz stateA.good.live.hs
  have lower : ¬ flush.toInt < 0 := by rcases flag with rfl | rfl <;> decide
  have upper : ¬ 5 < flush.toInt := by rcases flag with rfl | rfl <;> decide
  refine ⟨used, written, rc, after, z', result, run, stateA, buffersA, stateA.good, accountA, bytesA,
    inputA, outputA, allowed, ?_, ?_, controls.2, shapeA, frameA, liveA, allocA, nextA⟩
  · simpa only [lower, upper, false_or] using controls.1
  · intro impossible
    exact False.elim (impossible.elim lower upper)

/-- The scoped ordinary public contract also includes every out-of-range signed flush refusal, with its exact unchanged heap. Other valid flags remain open. -/
theorem DefaultFinishBoundary.ordinary_or_invalid_request_contract {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) ∨ (flush.toInt < 0 ∨ 5 < flush.toInt)) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with ordinary | invalid
  · exact boundary.ordinary_request_contract flush ordinary buffers raw
  · have bad : flush > Z_BLOCK ∨ flush < 0 := by
      rcases invalid with low | high
      · exact Or.inr (Int32.lt_iff_toInt_lt.mpr low)
      · exact Or.inl (Int32.lt_iff_toInt_lt.mpr high)
    have run := public_bad_flush_refusal boundary.good flush bad
    have account : StreamAccounting z z 0 0 := stream_accounting_zero z
    have data : Bytes h z.next_out 0 [] := by
      rcases raw with null | ⟨ob, oo, pointer⟩
      · exact Or.inl ⟨null, rfl, rfl⟩
      · obtain ⟨out, read, length⟩ := accounted_output_bytes boundary.good.live.hz buffers pointer account
        cases out with
        | nil => exact read
        | cons _ _ => simp at length
    have frame : BufferFrame h h (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, 0⟩] := by
      rcases raw with null | ⟨ob, oo, pointer⟩
      · rw [null]
        exact null_output_buffer_frame (full_storage_refl h _).2.1
      · exact RawOutputInterval.buffer_frame boundary.good boundary.good buffers buffers pointer account (Shape.refl h)
          (full_storage_refl h _).2.1 (RawOutputInterval.of_same rfl)
    refine ⟨0, [], Z_STREAM_ERROR, h, z, d, run, boundary, buffers, boundary.good, account, data,
      ?_, ?_, Or.inr (Or.inr (Or.inl rfl)), ?_, (fun _ => ⟨rfl, rfl⟩), ?_,
      Shape.refl h, frame, full_shape_live_change (Shape.refl h), rfl, rfl⟩
    · simp
    · simp
    · exact ⟨fun _ => invalid.elim Or.inl (fun high => Or.inr (Or.inl high)), fun _ => rfl⟩
    · intro impossible
      cases (show Z_STREAM_ERROR ≠ Z_STREAM_END from by decide) impossible

end Zlib.Deflate.Engine.Proofs
