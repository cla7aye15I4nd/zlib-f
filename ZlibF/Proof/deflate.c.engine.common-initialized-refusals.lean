import ZlibF.Proof.«deflate.c.engine.common-initialized-encoding-state»

/-! # Initial and post-header refusals preserve the same common-level history -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Reducing the actual public source to its error macro preserves the
entire encoding state and produces exactly zero bytes in every phase. -/
theorem CommonInitializedEncodingState.error_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush err : Int32) (source : deflate (some r) flush h = ERR_RETURN (some r) err h) :
    ∃ after z', deflate (some r) flush h = .ok (err, after) ∧
      CommonInitializedEncodingState after r ds z' d config accepted observed ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] := by
  obtain ⟨message, refused⟩ := err_return_run state.good.live.hz err
  let next := {z with msg := message}
  have goodA := stream_control_good (z' := next) state.good rfl state.good.live.zalloc state.good.live.zfree
  have accountA : StreamAccounting z next 0 0 := stream_accounting_zero z
  have buffersA := stream_control_buffers state.good goodA buffers accountA
  have run := source.trans refused
  have reachableA : StreamReachable .deflate (r.put h next) r := by
    apply StreamReachable.step (call := .deflate (some r) flush) (value := err) state.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header state.good state.no_header⟩
    · simp only [Call.execute, heapCall, run, next]
  have stateA := state.message_update message goodA reachableA
  have bytesA := caller_output_zero_slice (z := {z with msg := message}) goodA buffersA
  exact ⟨_, _, run, stateA, buffersA, accountA, bytesA⟩

/-- All pre-store stream and zero-output refusals retain the same observed
input/output history, including completed streams and partial headers. -/
theorem CommonInitializedEncodingState.entry_refusals {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush : Int32) (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0) :
    ∃ rc after z', (rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      deflate (some r) flush h = .ok (rc, after) ∧
      CommonInitializedEncodingState after r ds z' d config accepted observed ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] := by
  by_cases bad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · obtain ⟨after, z', run, stateA, buffersA, accountA, bytesA⟩ :=
      state.error_source buffers flush Z_STREAM_ERROR
        (public_stream_guard_refusal state.good flush flagLo flagHi bad)
    exact ⟨Z_STREAM_ERROR, after, z', Or.inl rfl, run, stateA, buffersA, accountA, bytesA⟩
  · have out : z.next_out ≠ .null := fun eq => bad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => bad (Or.inr (Or.inl ⟨count, eq⟩))
    have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
      intro status
      by_cases same : flush = Z_FINISH
      · exact same
      · exact False.elim (bad (Or.inr (Or.inr ⟨status, same⟩)))
    have empty : z.avail_out = 0 := by
      rcases refused with wrong | wrong | wrong | empty
      · exact False.elim (out wrong)
      · exact False.elim (valid wrong.1 wrong.2)
      · exact False.elim (wrong.2 (finish wrong.1))
      · exact empty
    obtain ⟨after, z', run, stateA, buffersA, accountA, bytesA⟩ :=
      state.error_source buffers flush Z_BUF_ERROR
        (public_zero_output_refusal state.good flush flagLo flagHi out valid finish empty)
    exact ⟨Z_BUF_ERROR, after, z', Or.inr rfl, run, stateA, buffersA, accountA, bytesA⟩

end Zlib.Deflate.Engine.Proofs
