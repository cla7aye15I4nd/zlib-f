import ZlibF.Proof.«inffast.c.frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inffast Zlib.Inffast.Proofs
set_option autoImplicit false

/-- Pure byte-array equality outside one segment. This is an internal
observation of the actual copy arrays, not a caller assumption. -/
def ArraySegmentFrame (before after : Array UInt8)
    (start count : Nat) : Prop :=
  ∀ j, j < start ∨ start + count ≤ j → after[j]? = before[j]?

theorem ArraySegmentFrame.blit
    (source : Array UInt8) (count sourceOff outputOff : Nat)
    (output : Array UInt8) :
    ArraySegmentFrame output
      (blitN source count sourceOff outputOff output)
      outputOff count := by
  intro j outside
  exact blitN_frame source count sourceOff outputOff output j outside

theorem ArraySegmentFrame.cpy
    (count sourceOff outputOff : Nat) (output : Array UInt8) :
    ArraySegmentFrame output
      (cpyN count sourceOff outputOff output)
      outputOff count := by
  intro j outside
  exact cpyN_frame count sourceOff outputOff output j outside

theorem ArraySegmentFrame.trans
    {first second third : Array UInt8}
    {start firstCount secondCount : Nat}
    (left : ArraySegmentFrame first second start firstCount)
    (right : ArraySegmentFrame second third
      (start + firstCount) secondCount) :
    ArraySegmentFrame first third start
      (firstCount + secondCount) := by
  intro j outside
  have beforeFirst : j < start ∨ start + firstCount ≤ j := by
    rcases outside with before | after
    · exact Or.inl before
    · exact Or.inr (by omega)
  have afterSecond : j < start + firstCount ∨
      start + firstCount + secondCount ≤ j := by
    rcases outside with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact (right j afterSecond).trans (left j beforeFirst)

theorem ArraySegmentFrame.widen
    {first second : Array UInt8}
    {start count wideStart wideCount : Nat}
    (frame : ArraySegmentFrame first second start count)
    (lower : wideStart ≤ start)
    (upper : start + count ≤ wideStart + wideCount) :
    ArraySegmentFrame first second wideStart wideCount := by
  intro j outside
  apply frame
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

#print axioms ArraySegmentFrame.blit
#print axioms ArraySegmentFrame.cpy
#print axioms ArraySegmentFrame.trans
#print axioms ArraySegmentFrame.widen

end Zlib.Inflate.Proofs
