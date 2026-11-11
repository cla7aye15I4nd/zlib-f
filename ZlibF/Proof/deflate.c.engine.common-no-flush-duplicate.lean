import ZlibF.Proof.«deflate.c.engine.no-flush-duplicate»
import ZlibF.Proof.«deflate.c.engine.common-entry-refusals»

/-! # Common-level duplicate NO_FLUSH refusal -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual duplicate request preserves the working phase. -/
theorem CommonSlowFinishBoundary.duplicate_no_flush {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (input : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0) (lower : 0 ≤ d.last_flush.toInt) :
    ∃ after z', deflate (some r) Z_NO_FLUSH h = .ok (Z_BUF_ERROR, after) ∧
      CommonSlowFinishBoundary after r ds z' { d with last_flush := Z_NO_FLUSH } config ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 0 := by
  have working : ∃ input origin base xs,
      BufferedBoundary h r ds z d input origin base xs config := by
    rcases boundary.phase with working | finishing
    · obtain ⟨input, origin, base, xs, state, _status⟩ := working
      exact ⟨input, origin, base, xs, state⟩
    · have impossible := finishing.status.symm.trans status
      cases (show FINISH_STATE ≠ BUSY_STATE from by decide) impossible
  obtain ⟨inputBytes, origin, base, xs, state⟩ := working
  have state0 := last_flush_buffered_boundary state Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  obtain ⟨message, refused⟩ := err_return_run state0.good.live.hz Z_BUF_ERROR
  let z' := { z with msg := message }
  have goodA := stream_control_good (z' := z') state0.good rfl boundary.good.live.zalloc boundary.good.live.zfree
  have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
  have buffersA := stream_control_buffers state0.good goodA buffers0 account
  have stateA := stream_control_buffered state0 goodA
  have run := (public_busy_no_flush_duplicate_source boundary.good status input pending out positive lower boundary.upper).trans refused
  have reachableA : StreamReachable .deflate (r.put (setD h ds { d with last_flush := Z_NO_FLUSH }) z') r := by
    apply StreamReachable.step (call := .deflate (some r) Z_NO_FLUSH) (value := Z_BUF_ERROR) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simp only [Call.execute, heapCall, run, z']
  exact ⟨_, z', run, ⟨goodA, reachableA, boundary.configuration,
    Or.inl ⟨inputBytes, origin, base, xs, stateA, status⟩, by change -2 ≤ (0 : Int); decide, by change (0 : Int) ≤ 5; decide⟩, buffersA, account⟩


end Zlib.Deflate.Engine.Proofs
