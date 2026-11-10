import ZlibF.Proof.«deflate.c.engine.block-request-effects»
import ZlibF.Proof.«deflate.c.engine.public-output-bytes»

/-! # Precise BufferFrame for every actual initialized BLOCK request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual default BLOCK request returns its produced-byte slice,
precise public BufferFrame, wrapping totals and unchanged allocation/live
ledger. All capacities, pending/initial phases and refusal cases are
included for null/raw-array output, level 6, memLevel 8 and the zlib wrapper.
Other flags, embedded output, advanced APIs and encoded correctness remain
separate; this does not replace Goal.deflate. -/
theorem DefaultFinishBoundary.block_request_with_buffer_frame {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      deflate (some r) Z_BLOCK h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed⟩ := boundary.block_total buffers raw
  rcases raw with null | ⟨ob, oo, pointer⟩
  · obtain ⟨rfl, rfl⟩ := boundary.legal_null_output_run_counts buffers (by decide) (by decide) null run stateA.good.live.hz account
    have totals := boundary.entry_refusal_run_counter_effects (by decide) (by decide) (Or.inl null) run stateA.good.live.hz account
    obtain ⟨shape, frame, live, alloc, next⟩ := boundary.entry_refusal_run_full_storage (by decide) (by decide) (Or.inl null) run
    have privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
      full_frame_weaken frame (fun _ root => Or.inl root)
    have exactFrame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, 0⟩] := by
      rw [null]
      exact null_output_buffer_frame privateFrame
    exact ⟨0, [], rc, after, z', result, run, stateA, buffersA, stateA.good, account,
      Or.inl ⟨null, rfl, rfl⟩, totals.1, totals.2, allowed, shape, exactFrame, live, alloc, next⟩
  · obtain ⟨inputA, outputA, interval, shape, frame, live, alloc, next⟩ :=
      boundary.block_raw_run_effects buffers pointer run stateA.good.live.hz account
    obtain ⟨written, data, length⟩ := accounted_output_bytes stateA.good.live.hz buffersA pointer account
    have exactFrame := interval.buffer_frame boundary.good stateA.good buffers buffersA pointer account shape frame
    rw [← length] at account data outputA exactFrame
    exact ⟨used, written, rc, after, z', result, run, stateA, buffersA, stateA.good, account,
      data, inputA, outputA, allowed, shape, exactFrame, live, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
