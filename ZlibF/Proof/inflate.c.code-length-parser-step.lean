import ZlibF.Proof.«inflate.c.code-length-repeat-contents»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- Partial parsing expressed solely by the independent CodeLens relation.
A completion of the returned prefix/bit stream is also a completion of the
incoming prefix/bit stream. This is not a specification of a called program.
At the loop's completed counter, CodeLens.done supplies the completion. -/
def LengthParserStep (alphabet : List Nat) (total : Nat) (before : InflateState)
    (input : List Bool) (state : InflateState) (remaining : List Bool) : Prop :=
  ∀ suffix lengths, CodeLens alphabet total (actualLengthPrefix state) remaining suffix lengths →
    CodeLens alphabet total (actualLengthPrefix before) input suffix lengths

theorem LengthParserStep.refl (alphabet : List Nat) (total : Nat) (s : InflateState) (input : List Bool) :
    LengthParserStep alphabet total s input s input := fun _ _ completion => completion

theorem LengthParserStep.trans {alphabet : List Nat} {total : Nat}
    {first second third : InflateState} {input middle remaining : List Bool}
    (left : LengthParserStep alphabet total first input second middle)
    (right : LengthParserStep alphabet total second middle third remaining) :
    LengthParserStep alphabet total first input third remaining :=
  fun suffix lengths completion => left suffix lengths (right suffix lengths completion)

/-- A completed real counter turns the partial parse relation into a full
independent CodeLens derivation. It supplies the relation's final witness. -/
theorem LengthParserStep.complete {alphabet : List Nat} {total : Nat}
    {before state : InflateState} {input remaining : List Bool}
    (step : LengthParserStep alphabet total before input state remaining)
    (finished : state.«have».toNat = total) :
    CodeLens alphabet total (actualLengthPrefix before) input remaining (actualLengthPrefix state) := by
  apply step
  apply CodeLens.done
  simpa only [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf_length] using finished

#print axioms LengthParserStep.complete
end Zlib.Inflate.Proofs
