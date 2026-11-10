import ZlibF.Proof.«inflate.c.symbols-retained-context»
import ZlibF.Proof.Format.Token

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C ZlibF.Spec Zlib.Inflate.Proofs.SlowInputFragment ZlibF.Math.LZ77History
set_option autoImplicit false

/-- An actually accepted token over the physical retained dictionary
reconstructs the original token over dictionary plus all prior output.
No complete Symbols continuation or future input is required. -/
theorem token_expand_retained_context
    {L D : List Nat} {dict past history next : List UInt8} {input rest : List Bool} {done : Bool}
    (parsed : Token.Step L D ((dict ++ past).drop ((dict ++ past).length - 32768))
      history input rest next done) :
    Token.Step L D dict (past ++ history) input rest (past ++ next) done := by
  cases parsed with
  | literal decoded small =>
    simpa only [List.append_assoc] using
      (Token.Step.literal (D := D) (dict := dict) (history := past ++ history) decoded small)
  | @copy _ _ _ _ symbol distance extraLength extraDistance decoded lower upper
      readLength decodedDistance distanceBound readDistance fits =>
    let parsedCopy : CopySyntax L D := ⟨input, _, _, _, rest, symbol, distance, extraLength, extraDistance,
      decoded, lower, upper, readLength, decodedDistance, distanceBound, readDistance⟩
    have positive := parsedCopy.distance_bounds.1
    change 1 ≤ distBases.getD distance 0 + extraDistance at positive
    have retainedFits : distBases.getD distance 0 + extraDistance ≤
        ((dict ++ past).drop ((dict ++ past).length - 32768)).length + history.length := by
      simpa only [List.length_append] using fits
    have copied := retained_history_agrees dict past history
      ((dict ++ past).drop ((dict ++ past).length - 32768))
      (distBases.getD distance 0 + extraDistance) (lengthBases.getD (symbol - 257) 0 + extraLength)
      (List.drop_suffix _ _) (by omega) retainedFits
    have fitsFull : distBases.getD distance 0 + extraDistance ≤ (dict ++ (past ++ history)).length := by
      simp only [List.length_drop, List.length_append] at fits ⊢
      omega
    have token := Token.Step.copy decoded lower upper readLength decodedDistance distanceBound readDistance fitsFull
    rw [copied] at token
    exact token
  | eob decoded => exact .eob decoded

end Zlib.Inflate.Proofs.FunctionalEpoch
