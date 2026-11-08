import ZlibF.Proof.«inffast.c.frame»
import ZlibF.Proof.«inflate.c.fast-view-exact-frame-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inffast Zlib.Inffast.Proofs
open ZlibF.Spec.Public
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

theorem ArraySegmentFrame.blit_then_cpy
    (source : Array UInt8) (a b sourceOff copyOff j : Nat)
    (output : Array UInt8) :
    ArraySegmentFrame output
      (cpyN b copyOff (j + a)
        (blitN source a sourceOff j output)) j (a + b) := by
  exact (ArraySegmentFrame.blit source a sourceOff j output).trans
    (ArraySegmentFrame.cpy b copyOff (j + a)
      (blitN source a sourceOff j output))

theorem ArraySegmentFrame.blit_then_blit
    (source : Array UInt8) (a b sourceOff nextOff j : Nat)
    (output : Array UInt8) :
    ArraySegmentFrame output
      (blitN source b nextOff (j + a)
        (blitN source a sourceOff j output)) j (a + b) := by
  exact (ArraySegmentFrame.blit source a sourceOff j output).trans
    (ArraySegmentFrame.blit source b nextOff (j + a)
      (blitN source a sourceOff j output))

theorem ArraySegmentFrame.blit_blit_cpy
    (source : Array UInt8)
    (a b c sourceOff nextOff copyOff j : Nat)
    (output : Array UInt8) :
    ArraySegmentFrame output
      (cpyN c copyOff (j + a + b)
        (blitN source b nextOff (j + a)
          (blitN source a sourceOff j output)))
      j (a + b + c) := by
  simpa only [Nat.add_assoc] using
    (ArraySegmentFrame.blit_then_blit source a b
      sourceOff nextOff j output).trans
      (ArraySegmentFrame.cpy c copyOff (j + (a + b))
        (blitN source b nextOff (j + a)
          (blitN source a sourceOff j output)))

/-- Convert a source copy's exact segment equality and an existing broad
heap frame into the output prefix ending at the actual cursor. -/
theorem BufferFrame.narrow_to_segment_end
    {before after : Heap} {changed : Nat → Prop}
    {dest : BRef} {oo capacity j count : Nat}
    {old next : Array UInt8}
    (broad : BufferFrame before after changed
      [⟨.ref dest oo, capacity⟩])
    (oldGet : Space.get before dest = some old)
    (nextGet : Space.get after dest = some next)
    (current : oo ≤ j)
    (segment : ArraySegmentFrame old next j count) :
    BufferFrame before after changed
      [⟨.ref dest oo, j + count - oo⟩] := by
  apply BufferFrame.singleton_narrow broad oldGet nextGet
  intro p bound outside
  apply segment
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

#print axioms ArraySegmentFrame.blit
#print axioms ArraySegmentFrame.cpy
#print axioms ArraySegmentFrame.trans
#print axioms ArraySegmentFrame.widen
#print axioms ArraySegmentFrame.blit_then_cpy
#print axioms ArraySegmentFrame.blit_then_blit
#print axioms ArraySegmentFrame.blit_blit_cpy
#print axioms BufferFrame.narrow_to_segment_end

end Zlib.Inflate.Proofs
