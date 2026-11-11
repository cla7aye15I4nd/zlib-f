import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»
import ZlibF.Proof.«deflate.c.engine.common-finish-protocol»

/-! # Common-level parameter and zero-output refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Stream-only updates retain both post-header common phases. -/
theorem common_phase_stream_control {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config)
    (goodA : DGood (r.put h z') r ds z' d) :
    PublicFinishPhase (r.put h z') r ds z' d config := by
  rcases boundary.phase with ⟨input, origin, base, xs, state, status⟩ | finishing
  · exact Or.inl ⟨input, origin, base, xs, stream_control_buffered state goodA, status⟩
  · exact Or.inr finishing

/-- The actual error-message callee preserves the common phase boundary. -/
theorem public_common_entry_refusal_protocol {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} (flush err : Int32)
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (source : deflate (some r) flush h = ERR_RETURN (some r) err h) :
    ∃ message,
      let z' := { z with msg := message }
      let after := r.put h z'
      deflate (some r) flush h = .ok (err, after) ∧
      CommonSlowFinishBoundary after r ds z' d config ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 0 := by
  obtain ⟨message, refused⟩ := err_return_run boundary.good.live.hz err
  let z' := { z with msg := message }
  have goodA := stream_control_good (z' := z') boundary.good rfl boundary.good.live.zalloc boundary.good.live.zfree
  have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
  have buffersA := stream_control_buffers boundary.good goodA buffers account
  have phaseA := common_phase_stream_control boundary goodA
  have run := source.trans refused
  have reachableA : StreamReachable .deflate (r.put h z') r := by
    apply StreamReachable.step (call := .deflate (some r) flush) (value := err) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simp only [Call.execute, heapCall, run, z']
  exact ⟨message, run, ⟨goodA, reachableA, boundary.configuration, phaseA, boundary.lower, boundary.upper⟩, buffersA, account⟩


/-- All public entry refusals preserve the same initialized common boundary. -/
theorem CommonSlowFinishBoundary.entry_refusals {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} (flush : Int32)
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0) :
    ∃ err after z', (err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) ∧
      deflate (some r) flush h = .ok (err, after) ∧
      CommonSlowFinishBoundary after r ds z' d config ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 0 := by
  by_cases streamBad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · obtain ⟨message, run, stateA, buffersA, accountA⟩ := public_common_entry_refusal_protocol flush Z_STREAM_ERROR boundary buffers
      (public_stream_guard_refusal boundary.good flush flagLo flagHi streamBad)
    exact ⟨Z_STREAM_ERROR, _, _, Or.inl rfl, run, stateA, buffersA, accountA⟩
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
    obtain ⟨message, run, stateA, buffersA, accountA⟩ := public_common_entry_refusal_protocol flush Z_BUF_ERROR boundary buffers
      (public_zero_output_refusal boundary.good flush flagLo flagHi out valid finish empty)
    exact ⟨Z_BUF_ERROR, _, _, Or.inr rfl, run, stateA, buffersA, accountA⟩


end Zlib.Deflate.Engine.Proofs
