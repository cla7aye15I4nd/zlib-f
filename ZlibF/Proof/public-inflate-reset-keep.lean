import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.base»

namespace ZlibF.Spec.Public.InflateResetKeepProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- `int inflateResetKeep(z_streamp strm)` resets decode progress while retaining the window. -/
theorem resetkeep_public : Goal.inflateResetKeep := by
  intro h r i z s hv
  rcases hv with ⟨hz, hstate, hi, hback, ha, hf, hlo, hhi⟩
  have hl : Live h r i z s := ⟨hz, hi, hstate, hback, ⟨hlo, hhi⟩, ha, hf⟩
  by_cases hw : s.wrap = 0
  · simpa [C.run, setI, putInflate, resetKeepState, resetKeepStream, inflateResetState,
      inflateResetStream, hw] using resetKeep_run hl
  · simpa [C.run, setI, putInflate, resetKeepState, resetKeepStream, inflateResetState,
      inflateResetStream, hw, i2ul] using resetKeep_run hl

#print axioms resetkeep_public
end ZlibF.Spec.Public.InflateResetKeepProof
