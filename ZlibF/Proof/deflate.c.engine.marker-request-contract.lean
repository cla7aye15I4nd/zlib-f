import ZlibF.Proof.«deflate.c.engine.marker-request-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.marker-request-controls»

/-! # The complete scoped public contract for every marker request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized default PARTIAL/SYNC/FULL request has the public safety, accounting,
precise BufferFrame and return-control clauses on the same actual returned
heap. Scope is level 6, memLevel 8, zlib wrapping and null/raw caller output.
All input counts, capacities, pending phases, first headers and refusal
branches are included. Embedded output, advanced APIs
and encoded-output correctness remain separate from this scoped result. -/
theorem DefaultFinishBoundary.marker_request_contract {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) :
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
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, goodA, accountA, bytesA,
      inputA, outputA, allowed, shapeA, frameA, liveA, allocA, nextA⟩ := boundary.marker_request_with_buffer_frame buffers raw flush flag
  have controls := boundary.marker_run_controls buffers raw flush flag run
  have low : ¬ flush.toInt < 0 := by rcases flag with rfl | rfl | rfl <;> decide
  have high : ¬ 5 < flush.toInt := by rcases flag with rfl | rfl | rfl <;> decide
  have ended : rc ≠ Z_STREAM_END := by
    intro endCode
    rcases allowed with ok | error | buf
    · exact (show Z_OK ≠ Z_STREAM_END from by decide) (ok.symm.trans endCode)
    · exact (show Z_STREAM_ERROR ≠ Z_STREAM_END from by decide) (error.symm.trans endCode)
    · exact (show Z_BUF_ERROR ≠ Z_STREAM_END from by decide) (buf.symm.trans endCode)
  exact ⟨used, written, rc, after, z', result, run, stateA, buffersA, goodA, accountA, bytesA,
    inputA, outputA, allowed.elim Or.inl (fun err => Or.inr (Or.inr err)),
    by simpa only [low, high, false_or] using controls,
    fun impossible => False.elim (impossible.elim low high),
    fun impossible => False.elim (ended impossible), shapeA, frameA, liveA, allocA, nextA⟩

end Zlib.Deflate.Engine.Proofs
