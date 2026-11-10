import ZlibF.Proof.«deflate.c.engine.encoded-state»
import ZlibF.Proof.«deflate.c.engine.refusal-checksum»

/-! # Early refusals retain the complete observed encoding state -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A stream-record store retains the exact completed pending suffix. -/
theorem FinishedEncoding.put_stream {h : Heap} {d : DeflateState} {accepted published : List UInt8}
    (encoding : FinishedEncoding h d accepted published) (r : ZStreamRef) (z' : ZStream) :
    FinishedEncoding (r.put h z') d accepted published := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  refine ⟨encoding.bits, tailBytes, ?_, meaning⟩
  rcases data with null | ⟨ref, offset, array, pointer, get, bound, slice⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, offset, array, pointer, (byte_get_stream_put h r z' ref).trans get, bound, slice⟩

/-- An actual message-only update transports every encoding phase. The
protocol on the returned heap is supplied by the structural execution
proof; all content and history facts are retained here. -/
theorem DefaultEncodingState.message_update {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (message : BPtr)
    (protocolA : DefaultFinishBoundary (r.put h {z with msg := message}) r ds {z with msg := message} d config) :
    DefaultEncodingState (r.put h {z with msg := message}) r ds {z with msg := message} d config accepted observed := by
  refine ⟨protocolA, state.checksum, ?_⟩
  rcases state.phase with ⟨emptyInput, emptyOutput, input, start, boundary⟩ |
      ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · exact Or.inl ⟨emptyInput, emptyOutput, input, start.put_stream protocolA.good rfl,
      stream_control_buffered boundary protocolA.good⟩
  · exact Or.inr (Or.inl ⟨emptyInput, headerOutput, input, stream_control_buffered boundary protocolA.good,
      status, encoding.put_stream r _⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨input, origin, base, xs, published, outputEq,
      stream_control_buffered boundary protocolA.good, status, encoding.put_stream r _, inputEq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨published, outputEq, phase, encoding.put_stream r _⟩))

/-- Reducing the actual public source to its error macro preserves the
entire encoding state and produces exactly zero bytes in every phase. -/
theorem DefaultEncodingState.error_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush err : Int32) (source : deflate (some r) flush h = ERR_RETURN (some r) err h) :
    ∃ after z', deflate (some r) flush h = .ok (err, after) ∧
      DefaultEncodingState after r ds z' d config accepted observed ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] := by
  obtain ⟨message, run, protocolA, buffersA, accountA⟩ :=
    public_entry_refusal_protocol flush err state.protocol buffers source
  have stateA := state.message_update message protocolA
  have bytesA := caller_output_zero_slice (z := {z with msg := message}) protocolA.good buffersA
  exact ⟨_, _, run, stateA, buffersA, accountA, bytesA⟩

/-- All pre-store stream and zero-output refusals retain the same observed
input/output history, including completed streams and partial headers. -/
theorem DefaultEncodingState.entry_refusals {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush : Int32) (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0) :
    ∃ rc after z', (rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultEncodingState after r ds z' d config accepted observed ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] := by
  by_cases bad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · obtain ⟨after, z', run, stateA, buffersA, accountA, bytesA⟩ :=
      state.error_source buffers flush Z_STREAM_ERROR
        (public_stream_guard_refusal state.protocol.good flush flagLo flagHi bad)
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
        (public_zero_output_refusal state.protocol.good flush flagLo flagHi out valid finish empty)
    exact ⟨Z_BUF_ERROR, after, z', Or.inr rfl, run, stateA, buffersA, accountA, bytesA⟩

end Zlib.Deflate.Engine.Proofs
