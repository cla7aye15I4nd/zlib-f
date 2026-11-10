import ZlibF.Proof.«inflate.c.fast-future-representation-callee-v2»
import ZlibF.Proof.«inflate.c.output-credit-append»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- The exact actual output frame splits a full physical current-call
observation into the old prefix and this invocation's newly written slice. -/
theorem fast_segment_of_whole
    {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {off oldCount made : Nat}
    {oldArray array : Array UInt8} {old whole : List UInt8}
    (frame : BufferFrame before after changed [⟨.ref ref off, made⟩])
    (beforeGet : Space.get before ref = some oldArray)
    (afterGet : Space.get after ref = some array)
    (start : oldCount ≤ off)
    (oldBound : off ≤ oldArray.size)
    (newBound : off + made ≤ array.size)
    (oldLength : old.length = oldCount)
    (oldBytes : ZlibF.Math.LZ77Copy.writtenBytes oldArray off oldCount = old)
    (wholeBytes : ZlibF.Math.LZ77Copy.writtenBytes array (off + made)
      (oldCount + made) = whole) :
    ∃ more : List UInt8,
      more.length = made ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = more ∧
      whole = old ++ more := by
  let more := ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made
  have moreLength : more.length = made := by
    simp only [more, ZlibF.Math.LZ77Copy.writtenBytes,
      List.length_take, List.length_drop, Array.length_toList]
    omega
  have realFrame : BufferFrame before after changed
      [⟨.ref ref off, more.length⟩] := by
    simpa only [moreLength] using frame
  have observed := physical_output_append (old:=old) (more:=more) realFrame beforeGet afterGet
    (by omega) oldBound (by simpa only [oldLength] using oldBytes) (by simpa only [moreLength] using (show ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = more from rfl))
  refine ⟨more, moreLength, rfl, ?_⟩
  have count : (old ++ more).length = oldCount + made := by
    simp only [List.length_append, oldLength, moreLength]
  rw [count, moreLength] at observed
  exact wholeBytes.symm.trans observed

#print axioms fast_segment_of_whole
end Zlib.Inflate.Proofs.FunctionalEpoch
