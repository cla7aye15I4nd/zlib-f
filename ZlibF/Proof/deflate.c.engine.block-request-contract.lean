import ZlibF.Proof.«deflate.c.engine.block-request-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.block-request-controls»

/-! # Scoped public BLOCK safety, frame, accounting and control contract -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized default BLOCK request has the public safety, accounting,
precise BufferFrame and return-control clauses on the same actual returned
heap. Scope is level 6, memLevel 8, zlib wrapping and null/raw caller output.
All input counts, capacities, pending phases, first headers and refusal
branches are included. Other valid flags, embedded output, advanced APIs
and encoded-output correctness remain separate from this scoped result. -/
theorem DefaultFinishBoundary.block_request_contract {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) Z_BLOCK) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ Z_BLOCK.toInt < 0 ∨ 5 < Z_BLOCK.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ Z_BLOCK ≠ Z_FINISH)) ∧
      (Z_BLOCK.toInt < 0 ∨ 5 < Z_BLOCK.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → Z_BLOCK = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, goodA, accountA, bytesA,
      inputA, outputA, allowed, shapeA, frameA, liveA, allocA, nextA⟩ := boundary.block_request_with_buffer_frame buffers raw
  have controls := boundary.block_run_controls buffers raw run
  have low : ¬ Z_BLOCK.toInt < 0 := by decide
  have high : ¬ 5 < Z_BLOCK.toInt := by decide
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
