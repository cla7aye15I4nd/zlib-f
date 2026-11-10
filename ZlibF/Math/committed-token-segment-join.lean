import ZlibF.Math.InflateCommittedTokens
namespace ZlibF.Math.InflateCommittedTokens
open ZlibF.Spec
set_option autoImplicit false

/-- Independently executed slow/fast segments compose their actual
committed words. A new fast call may start with an empty local word
without resetting the enclosing block's parser context. -/
theorem Committed.trans
    {L D : List Nat} {dict start middle final : List UInt8} {firstWord secondWord : List Bool}
    (first : Committed L D dict start firstWord middle)
    (second : Committed L D dict middle secondWord final) :
    Committed L D dict start (firstWord ++ secondWord) final := by
  intro future rest output
  have combined := (first (secondWord ++ future) rest output).trans (second future rest output)
  simpa only [List.append_assoc, List.nil_append] using combined

/-- An actual EOB grammar from a later segment closes the original block
prefix; no valid future or desired final output is assumed. -/
theorem Committed.complete_segment
    {L D : List Nat} {dict start middle output : List UInt8}
    {firstWord segment rest : List Bool}
    (first : Committed L D dict start firstWord middle)
    (ended : Symbols L D dict middle segment rest output) :
    Symbols L D dict start (firstWord ++ segment) rest output :=
  (first.future segment rest output).mpr ended

end ZlibF.Math.InflateCommittedTokens
