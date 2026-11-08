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

/-- A whole-object frame preserves an admitted byte view when its
allocation root lies outside the frame's allowed changes. -/
theorem frame_byte_view_get
    {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {off : Nat}
    (frame : Frame before after changed)
    (get : Space.get before ref = some array)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b) :
    Space.get after ref = some array := by
  have slots := frame.2.2.2.2.2
  cases ref with
  | blk b =>
    have live : before.live b := by simp [Heap.live, show before.bytes b = some array from get]
    exact (slots b live (outside b rfl)).1.trans get
  | dstate_depth b =>
    cases state : before.dstates b with
    | none => simp [Space.get, state] at get
    | some value =>
      have live : before.live b := by simp [Heap.live, state]
      have same := slots b live (outside b rfl)
      change (after.dstates b).map (·.depth) = some array
      rw [same.2.2.2.2.1]
      exact get
  | str text => exact get
  | st_dist_code => change some after.static.dist_code = some array; rw [← frame.1]; exact get
  | st_length_code => change some after.static.length_code = some array; rw [← frame.1]; exact get

/-- Restoring the output view in a caller frame cannot hide a change to
a different admitted input view. -/
theorem BufferFrame.other_view_get
    {before after : Heap} {changed : Nat → Prop}
    {source dest : BRef} {input output : Array UInt8} {readOff writeOff capacity : Nat}
    (frame : BufferFrame before after changed [⟨.ref dest writeOff, capacity⟩])
    (inputGet : Space.get before source = some input)
    (outputGet : Space.get before dest = some output)
    (outside : ∀ b, ByteRoot (.ref source readOff) b → ¬ changed b)
    (different : source ≠ dest) :
    Space.get after source = some input := by
  have same := frame_byte_view_get frame.1 inputGet outside
  have restored : restoreRegions before after [⟨.ref dest writeOff, capacity⟩] =
      Space.put after dest output := by simp [restoreRegions, outputGet]
  rw [restored, byte_view_get_put_ne after different output] at same
  exact same

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
    (separate : source ≠ dest ∨ readOff + count ≤ writeOff ∨ writeOff + capacity ≤ readOff) :
    Bytes after (.ref source readOff) count ((input.toList.drop readOff).take count) := by
  by_cases shared : source = dest
  · subst source
    have order : readOff + count ≤ writeOff ∨ writeOff + capacity ≤ readOff := by
      rcases separate with different | order
      · exact False.elim (different rfl)
      · exact order
    exact BufferFrame.same_view_read frame inputGet bound order
  · exact Or.inr ⟨source, readOff, input, rfl,
      BufferFrame.other_view_get frame inputGet outputGet outside shared, bound, rfl⟩

#print axioms frame_byte_view_get
#print axioms BufferFrame.other_view_get
#print axioms BufferFrame.input_read

#print axioms BufferFrame.same_view_read
end Zlib.Inflate.Proofs
