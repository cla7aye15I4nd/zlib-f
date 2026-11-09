import ZlibF.Proof.«inflate.c.stored-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller input slice outside the permitted output interval retains
its byte values, even when both occupy the same represented byte object. -/
theorem BufferFrame.same_view_read
    {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {readOff count writeOff capacity : Nat}
    (frame : BufferFrame before after changed [⟨.ref ref writeOff, capacity⟩])
    (get : Space.get before ref = some array)
    (bound : readOff + count ≤ array.size)
    (separate : readOff + count ≤ writeOff ∨ writeOff + capacity ≤ readOff) :
    Bytes after (.ref ref readOff) count ((array.toList.drop readOff).take count) := by
  obtain ⟨current, currentGet, size, outside⟩ :=
    frame.2 ⟨.ref ref writeOff, capacity⟩ (by simp) ref writeOff array rfl get
  have slice : (current.toList.drop readOff).take count =
      (array.toList.drop readOff).take count := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, Array.length_toList]
      omega
    · intro index inCurrent inArray
      have short : index < count := by
        have lengthBound := inArray
        simp only [List.length_take] at lengthBound
        omega
      have indexBound : readOff + index < array.size := by
        omega
      have outsideRegion : ¬ ∃ region : Region,
          region ∈ [⟨.ref ref writeOff, capacity⟩] ∧ region.covers ref (readOff + index) := by
        rintro ⟨region, member, covered⟩
        have same : region = (⟨.ref ref writeOff, capacity⟩ : Region) := by simpa using member
        subst region
        obtain ⟨base, pointer, lower, upper⟩ := covered
        have baseEq : writeOff = base := (Ptr.ref.inj pointer).2
        dsimp only at lower upper
        rcases separate with left | right <;> omega
      have point := outside (readOff + index) indexBound outsideRegion
      have currentBound : readOff + index < current.size := by omega
      have equal : current[readOff + index] = array[readOff + index] := by
        rw [Array.getElem?_eq_getElem currentBound, Array.getElem?_eq_getElem indexBound] at point
        exact Option.some.inj point
      simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using equal
  exact Or.inr ⟨ref, readOff, current, rfl, currentGet, by omega, slice.symm⟩

/-- A whole-object frame preserves an admitted byte view outside its
allowed allocation changes when the external borrow is stable. -/
theorem frame_byte_view_get
    {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {off : Nat}
    (frame : Frame before after changed)
    (get : Space.get before ref = some array)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b)
    (stable : C.LibcBorrow.BorrowStable before after ref) :
    Space.get after ref = some array :=
  BorrowedViews.frame_get frame get outside stable

/-- Restoring the output view in a caller frame cannot hide a change to
a different admitted input view. -/
theorem BufferFrame.other_view_get
    {before after : Heap} {changed : Nat → Prop}
    {source dest : BRef} {input output : Array UInt8} {readOff writeOff capacity : Nat}
    (frame : BufferFrame before after changed [⟨.ref dest writeOff, capacity⟩])
    (inputGet : Space.get before source = some input)
    (outputGet : Space.get before dest = some output)
    (outside : ∀ b, ByteRoot (.ref source readOff) b → ¬ changed b)
    (different : source ≠ dest) (stable : C.LibcBorrow.BorrowStable before after source) :
    Space.get after source = some input :=
  BorrowedViews.buffer_other_get frame inputGet outputGet outside different stable

/-- The full input slice survives the permitted output interval on any
represented byte references. This covers both distinct objects and two
disjoint intervals of one object. -/
theorem BufferFrame.input_read
    {before after : Heap} {changed : Nat → Prop}
    {source dest : BRef} {input output : Array UInt8}
    {readOff count writeOff capacity : Nat}
    (frame : BufferFrame before after changed [⟨.ref dest writeOff, capacity⟩])
    (inputGet : Space.get before source = some input)
    (outputGet : Space.get before dest = some output)
    (bound : readOff + count ≤ input.size)
    (outside : ∀ b, ByteRoot (.ref source readOff) b → ¬ changed b)
    (separate : source ≠ dest ∨ readOff + count ≤ writeOff ∨ writeOff + capacity ≤ readOff)
    (stable : C.LibcBorrow.BorrowStable before after source) :
    Bytes after (.ref source readOff) count ((input.toList.drop readOff).take count) := by
  by_cases shared : source = dest
  · subst source
    have order : readOff + count ≤ writeOff ∨ writeOff + capacity ≤ readOff := by
      rcases separate with different | order
      · exact False.elim (different rfl)
      · exact order
    exact BufferFrame.same_view_read frame inputGet bound order
  · exact Or.inr ⟨source, readOff, input, rfl,
      BufferFrame.other_view_get frame inputGet outputGet outside shared stable, bound, rfl⟩

#print axioms frame_byte_view_get
#print axioms BufferFrame.other_view_get
#print axioms BufferFrame.input_read

#print axioms BufferFrame.same_view_read
end Zlib.Inflate.Proofs
