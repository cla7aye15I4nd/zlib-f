import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Spec.Functional.Lifecycle

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec

namespace ZlibF.Spec.Public.InflateResetProof

theorem drop_matches_freewin (h : Heap) (p : BPtr) : dropWindow h p = freeWin h p := by
  cases p with
  | null => rfl
  | ref r off =>
    cases r <;> cases off <;> rfl

/-- `int inflateReset(z_streamp strm)`
The exact public result, state, frame and ownership contract. -/
theorem reset_public : Goal.inflateReset := by
  intro h r i z s hv hf hwin
  rcases hv with ⟨hz,hstate,hi,hback,ha,hfree,hlo,hhi⟩
  have hl : Live h r i z s := ⟨hz,hi,hstate,hback,⟨hlo,hhi⟩,ha,hfree⟩
  have hw : WindowOk h s.window := hwin
  have hr := inflateReset_run hl hf (Or.inr hw)
  by_cases hbits : s.wbits = s.reqbits
  · simpa [C.run, hbits, resetHeap, resetPre, inflateResetPre, resetKeepState,
      inflateResetState, resetKeepStream, inflateResetStream, setI, putInflate, i2ul] using hr
  · by_cases hwrap : s.reqwrap = 0
    · simpa [C.run, hbits, hwrap, drop_matches_freewin, resetHeap, resetPre, inflateResetPre, resetKeepState,
        inflateResetState, resetKeepStream, inflateResetStream, setI, putInflate, i2ul] using hr
    · simpa [C.run, hbits, hwrap, drop_matches_freewin, resetHeap, resetPre, inflateResetPre, resetKeepState,
        inflateResetState, resetKeepStream, inflateResetStream, setI, putInflate, i2ul] using hr

#print axioms reset_public

end ZlibF.Spec.Public.InflateResetProof
