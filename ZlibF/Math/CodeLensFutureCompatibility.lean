import ZlibF.Proof.Format.Deflate

namespace ZlibF.Spec.CodeLensFuture
open ZlibF.Spec.Proofs
set_option autoImplicit false

/-- An acceptable independent alphabet makes a successful symbol decode
stable under any suffix. This is the existing Ext theorem specialized to
one actual successful pure decode; no minimum input/root width is assumed. -/
theorem decodeSym_append {kind : CodeKind} {alphabet : List Nat}
    {current residual future : List Bool} {symbol : Nat}
    (valid : Acceptable kind alphabet)
    (decoded : decodeSym alphabet current = some (symbol, residual)) :
    decodeSym alphabet (current ++ future) = some (symbol, residual ++ future) :=
  ext_acceptable valid current symbol residual future decoded

/-- A current-prefix symbol decode and a complete-input symbol decode
with the same acceptable alphabet agree, including the residual suffix. -/
theorem decodeSym_current_full {kind : CodeKind} {alphabet : List Nat}
    {current residualCurrent residualFull future : List Bool} {symbolCurrent symbolFull : Nat}
    (valid : Acceptable kind alphabet)
    (currentDecode : decodeSym alphabet current = some (symbolCurrent, residualCurrent))
    (fullDecode : decodeSym alphabet (current ++ future) = some (symbolFull, residualFull)) :
    symbolCurrent = symbolFull ∧ residualCurrent ++ future = residualFull := by
  have same := Option.some.inj ((decodeSym_append valid currentDecode).symm.trans fullDecode)
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- Completion on current input determines exactly the same code lengths
as completion on current input plus future. Literal and every repeat
constructor are covered by the existing CodeLens append/determinism proof.
Alphabet acceptability is a format fact, not a new public caller condition. -/
theorem current_full {alphabet acc decodedCurrent decodedFull : List Nat} {total : Nat}
    {current residualCurrent residualFull future : List Bool}
    (valid : Acceptable .codeLength alphabet)
    (currentParse : CodeLens alphabet total acc current residualCurrent decodedCurrent)
    (fullParse : CodeLens alphabet total acc (current ++ future) residualFull decodedFull) :
    decodedCurrent = decodedFull ∧ residualCurrent ++ future = residualFull := by
  obtain ⟨rest, lengths⟩ := (currentParse.append (ext_acceptable valid) future).det fullParse
  exact ⟨lengths, rest⟩

/-- The same compatibility result needs only decoder extension stability.
This interface reuses an already established Ext fact directly. -/
theorem current_full_of_ext {alphabet acc decodedCurrent decodedFull : List Nat} {total : Nat}
    {current residualCurrent residualFull future : List Bool}
    (stable : Ext alphabet)
    (currentParse : CodeLens alphabet total acc current residualCurrent decodedCurrent)
    (fullParse : CodeLens alphabet total acc (current ++ future) residualFull decodedFull) :
    decodedCurrent = decodedFull ∧ residualCurrent ++ future = residualFull := by
  obtain ⟨rest, lengths⟩ := (currentParse.append stable future).det fullParse
  exact ⟨lengths, rest⟩

/-- Independent valid-future payload alphabet conditions transfer to the
current-input completed parse without assuming that the actual constructor
or following payload execution succeeds. -/
theorem payload_alphabets {alphabet acc decodedCurrent decodedFull : List Nat} {total nlen : Nat}
    {current residualCurrent residualFull future : List Bool}
    (valid : Acceptable .codeLength alphabet)
    (currentParse : CodeLens alphabet total acc current residualCurrent decodedCurrent)
    (fullParse : CodeLens alphabet total acc (current ++ future) residualFull decodedFull)
    (eob : HasEndOfBlock (decodedFull.take nlen))
    (validL : Acceptable .litLen (decodedFull.take nlen))
    (validD : Acceptable .dist (decodedFull.drop nlen)) :
    decodedCurrent = decodedFull ∧ residualCurrent ++ future = residualFull ∧
      HasEndOfBlock (decodedCurrent.take nlen) ∧
      Acceptable .litLen (decodedCurrent.take nlen) ∧ Acceptable .dist (decodedCurrent.drop nlen) := by
  obtain ⟨lengths, rest⟩ := current_full valid currentParse fullParse
  exact ⟨lengths, rest, lengths ▸ eob, lengths ▸ validL, lengths ▸ validD⟩

#print axioms decodeSym_append
#print axioms decodeSym_current_full
#print axioms current_full
#print axioms current_full_of_ext
#print axioms payload_alphabets
end ZlibF.Spec.CodeLensFuture
