import ZlibF.Proof.«inflate.c.meaning»

open ZlibF.Spec Zlib.Inflate.Proofs

/-! `case MATCH` leaves for want of output room before it checks the distance.
A raw inflate (windowBits -15, no dictionary) of the bytes `03 02` with no
output room stopped with `Z_OK` in `MATCH`, offset 1, length 3 and an empty
window; the next call with room reported "invalid distance too far back"
(`tests/goals/inflate-meaning-body/far-match.c`). Before P12 the grammar had
no position there: `.copy` was reached only by a match token, which needs the
distance within the history. The bytes hold a final fixed block, the length
symbol 257 (length 3) and the distance symbol 0 (distance 1). After the three
block header bits, the twelve bits of the match reach `.copy 3 1` through
`partialToken`, although the history is empty. -/
namespace UncheckedMatchRegression

/-- The twelve bits of the match: the fixed code of 257 (`0000001`) and the
fixed code of distance symbol 0 (`00000`). -/
def matchBits : List Bool :=
  [false, false, false, false, false, false, true] ++ [false, false, false, false, false]

/-- The input bytes are the block header, the match and one pad bit. -/
theorem input_bits :
    bytesToBits [0x03, 0x02] = [true, true, false] ++ matchBits ++ [false] := by
  decide

set_option maxRecDepth 100000 in
/-- The match is a parse position with nothing written, beyond the empty history. -/
theorem unchecked_match :
    DeflateParsed [] ([] ++ [true, true, false] ++ matchBits)
      ⟨[], true, .codes fixedLitLens fixedDistLens (.copy 3 1)⟩ := by
  refine DeflateParsed.partialToken matchBits (DeflateParsed.fixedHeader DeflateParsed.start)
    ⟨257, 0, 0, 0, [false, false, false, false, false], [false, false, false, false, false], [],
      ?_, by decide, by decide, rfl, ?_, by decide, rfl, rfl, rfl⟩
  · rfl
  · rfl

/-- The distance exceeds the empty history. -/
theorem beyond_history : (([] : List UInt8) ++ []).length < 1 := by decide

end UncheckedMatchRegression

#print axioms UncheckedMatchRegression.input_bits
#print axioms UncheckedMatchRegression.unchecked_match
