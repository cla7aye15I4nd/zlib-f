import ZlibF.Proof.«deflate.c.engine.public-refusal-full-storage»
import ZlibF.Proof.«deflate.c.engine.common-initialized-encoding-state»
import ZlibF.Proof.«deflate.c.engine.public-busy-full-storage»
import ZlibF.Proof.«deflate.c.engine.refusal-counters»

/-! # Complete heap frames for actual public refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual legal-flag entry refusal retains all objects outside the stream record. -/
theorem CommonInitializedEncodingState.entry_refusal_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32} {accepted observed : List UInt8}
    (boundary : CommonInitializedEncodingState h r ds z d config accepted observed)
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


end Zlib.Deflate.Engine.Proofs
