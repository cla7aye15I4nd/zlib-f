import ZlibF.Runtime.Schema

open C

/-! `ConsumesWithinStream` said that a call after which the whole valid stream is
consumed returns `Z_STREAM_END` or `Z_MEM_ERROR`. After a call that read a whole
zlib stream and returned `Z_STREAM_END`, a further call with a NULL `next_out`
consumes nothing and returns `Z_STREAM_ERROR`
(`tests/goals/inflate-meaning/refused-after-end.c`); its consumed input is still
the whole stream. The clause now says that such a call returns neither `Z_OK`
nor `Z_BUF_ERROR`, which is what every use needs. -/
namespace RefusedAfterEndRegression

/-- The refusal is allowed by the corrected clause and excluded by the old one. -/
theorem refusal_allowed :
    (Z_STREAM_ERROR ≠ Z_OK ∧ Z_STREAM_ERROR ≠ Z_BUF_ERROR) ∧
      ¬ (Z_STREAM_ERROR = Z_STREAM_END ∨ Z_STREAM_ERROR = Z_MEM_ERROR) := by decide

end RefusedAfterEndRegression
