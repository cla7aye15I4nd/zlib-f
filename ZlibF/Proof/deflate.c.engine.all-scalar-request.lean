import ZlibF.Proof.«deflate.c.engine.full-protocol»
import ZlibF.Proof.«deflate.c.engine.nonfull-request»

/-! # Every signed request returns from the same initialized default boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed request scalar, including all six valid flush flags and
invalid-scalar refusals, returns from the same actual default boundary.
No callee contract or successful-call premise is assumed. -/
theorem DefaultFinishBoundary.all_scalar_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) (flush : Int32) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  by_cases bad : flush.toInt < 0 ∨ 5 < flush.toInt
  · have badGuard : flush > Z_BLOCK ∨ flush < 0 := by
      rcases bad with low | high
      · exact Or.inr (Int32.lt_iff_toInt_lt.mpr low)
      · exact Or.inl (Int32.lt_iff_toInt_lt.mpr high)
    exact ⟨0, 0, Z_STREAM_ERROR, h, z, d, public_bad_flush_refusal boundary.good flush badGuard,
      boundary, buffers, stream_accounting_zero z, Or.inr (Or.inr (Or.inl rfl))⟩
  · by_cases full : flush = Z_FULL_FLUSH
    · subst flush
      obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed⟩ :=
        boundary.full_total buffers raw
      exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account,
        allowed.elim Or.inl (fun err => Or.inr (Or.inr err))⟩
    · have notThree : flush.toInt ≠ 3 := fun eq => full (Int32.toInt_inj.mp eq)
      have alternatives : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
          flush = Z_FINISH ∨ flush = Z_BLOCK := by
        simp only [← Int32.toInt_inj]
        change flush.toInt = 0 ∨ flush.toInt = 1 ∨ flush.toInt = 2 ∨ flush.toInt = 4 ∨ flush.toInt = 5
        omega
      exact boundary.nonfull_request buffers raw flush alternatives

end Zlib.Deflate.Engine.Proofs
