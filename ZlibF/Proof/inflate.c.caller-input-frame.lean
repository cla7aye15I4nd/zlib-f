import ZlibF.Proof.«inflate.c.buffer-frame-input»
import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller input slice outside the permitted output interval retains
its byte values, even when both occupy the same represented byte object. -/
theorem BufferFrame.same_view_separate_read
    {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {readOff count writeOff capacity : Nat}
    (frame : BufferFrame before after changed [⟨.ref ref writeOff, capacity⟩])
    (get : Space.get before ref = some array)
    (bound : readOff + count ≤ array.size)
    (separate : Separate (.ref ref readOff) count (.ref ref writeOff) capacity) :
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
        rcases separate with empty | empty | order
        · omega
        · omega
        · simp only [ne_eq, not_true_eq_false, false_or] at order
          omega
      have point := outside (readOff + index) indexBound outsideRegion
      have currentBound : readOff + index < current.size := by omega
      have equal : current[readOff + index] = array[readOff + index] := by
        rw [Array.getElem?_eq_getElem currentBound, Array.getElem?_eq_getElem indexBound] at point
        exact Option.some.inj point
      simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using equal
  exact Or.inr ⟨ref, readOff, current, rfl, currentGet, by omega, slice.symm⟩

/-- A readable caller byte object cannot be the stream record itself. -/
theorem caller_byte_root_not_stream {h : Heap} {r : ZStreamRef} {ds off b : Nat}
    {z : ZStream} {d : InflateState} {ref : BRef} {array : Array UInt8}
    (good : Good h r ds z d) (get : Space.get h ref = some array)
    (root : ByteRoot (.ref ref off) b) : ¬ StreamRoot r b := by
  have absent : h.streams b = none ∧ h.gzstates b = none := by
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      have slots := Uniq.bytes_only good.uniq get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some value =>
        have unique := good.uniq i
        simp only [state, cnt_some] at unique
        constructor
        · cases streamGet : h.streams i with
          | none => rfl
          | some value => simp only [streamGet, cnt_some] at unique; omega
        · cases gzGet : h.gzstates i with
          | none => rfl
          | some value => simp only [gzGet, cnt_some] at unique; omega
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root
  cases r with
  | tab i =>
    intro same
    change b = i at same
    have live := good.live.hz
    simp only [ZStreamRef.get, ← same, absent.1] at live
    contradiction
  | in_gzstate_strm i =>
    intro same
    change b = i at same
    have live := good.live.hz
    simp only [ZStreamRef.get, ← same, absent.2, Option.map_none] at live
    contradiction

/-- Caller ownership and the good heap derive the input exclusion needed
by the fast frame consumer. No allocation-identity premise is required. -/
theorem caller_byte_root_outside
    {h : Heap} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8}
    (good : Good h r zs z s) (get : Space.get h ref = some array)
    (range : CallerRange h r (.ref ref off) count false)
    (root : ByteRoot (.ref ref off) b) :
    ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream good get root stream
    · exact outside b root ((good.streamOwned_iff b).mpr owned)

/-- The permitted fast output interval leaves every byte of a disjoint
caller input range unchanged, including shared objects and empty ranges. -/
theorem caller_input_bytes_preserved
    {before after : Heap} {r : ZStreamRef} {zs writeOff capacity count : Nat}
    {z : ZStream} {s : InflateState} {p : BPtr} {dest : BRef}
    {output : Array UInt8} {xs : List UInt8}
    (good : Good before r zs z s)
    (range : CallerRange before r p count false)
    (outputGet : Space.get before dest = some output)
    (bytes : Bytes before p count xs)
    (separate : Separate p count (.ref dest writeOff) capacity)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, capacity⟩]) :
    Bytes after p count xs := by
  rcases bytes with null | ⟨source, off, input, pointer, get, bound, values⟩
  · exact Or.inl null
  · subst p
    have outside := fun b root => caller_byte_root_outside good get range (b := b) root
    by_cases shared : source = dest
    · subst source
      rw [values]
      exact BufferFrame.same_view_separate_read frame get bound separate
    · exact Or.inr ⟨source, off, input, rfl,
        BufferFrame.other_view_get frame get outputGet outside shared, bound, values⟩

#print axioms BufferFrame.same_view_separate_read
#print axioms caller_byte_root_outside
#print axioms caller_input_bytes_preserved
end Zlib.Inflate.Proofs
