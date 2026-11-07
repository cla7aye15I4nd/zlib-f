import ZlibF.Proof.«deflate.c.engine.public-entry-refusal-source»
import ZlibF.Proof.«deflate.c.engine.public-refusal-protocol»

/-! # Actual public stream and zero-output refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual pre-store stream-error and zero-output refusals retain the
initialized protocol, static error-message semantics and caller buffers. -/
theorem DefaultFinishBoundary.entry_refusals {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} (flush : Int32)
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0) :
    ∃ err after z', (err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) ∧
      deflate (some r) flush h = .ok (err, after) ∧
      DefaultFinishBoundary after r ds z' d config ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 0 := by
  by_cases streamBad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · obtain ⟨message, run, stateA, buffersA, accountA⟩ := public_entry_refusal_protocol flush Z_STREAM_ERROR boundary buffers
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
    obtain ⟨message, run, stateA, buffersA, accountA⟩ := public_entry_refusal_protocol flush Z_BUF_ERROR boundary buffers
      (public_zero_output_refusal boundary.good flush flagLo flagHi out valid finish empty)
    exact ⟨Z_BUF_ERROR, _, _, Or.inr rfl, run, stateA, buffersA, accountA⟩

end Zlib.Deflate.Engine.Proofs
