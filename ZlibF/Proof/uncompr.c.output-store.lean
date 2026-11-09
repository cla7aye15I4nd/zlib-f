import ZlibF.Proof.«uncompr.c.output-prefix»
import ZlibF.Proof.«uncompr.c.loop-objects»
import ZlibF.Proof.«uncompr.c.writeback-support»

namespace Zlib.Uncompr.Proof.OutputPrefix
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.Resources
set_option autoImplicit false

/-- Unchanged cells outside an interval give the exact three-slice array
replacement. No whole-allocation permission is substituted for the interval. -/
theorem array_eq_prefix_slice_suffix
    (before current : Array UInt8) (off count : Nat)
    (size : current.size = before.size) (room : off + count ≤ before.size)
    (outside : ∀ j, j < before.size → j < off ∨ off + count ≤ j → current[j]? = before[j]?) :
    current = before.extract 0 off ++ current.extract off (off + count) ++
      before.extract (off + count) before.size := by
  have first : current.extract 0 off = before.extract 0 off := by
    apply Array.ext
    · simp only [Array.size_extract, size]
    · intro j left right
      have short : j < off := by simp only [Array.size_extract] at right; omega
      have bounded : j < before.size := by omega
      have point := outside j bounded (Or.inl short)
      have currentBound : j < current.size := by omega
      rw [Array.getElem?_eq_getElem currentBound, Array.getElem?_eq_getElem bounded] at point
      simpa only [Array.getElem_extract, Nat.zero_add] using Option.some.inj point
  have last : current.extract (off + count) current.size = before.extract (off + count) before.size := by
    apply Array.ext
    · simp only [Array.size_extract, size]
    · intro j left right
      have bounded : off + count + j < before.size := by
        simp only [Array.size_extract, Nat.min_self] at right
        omega
      have point := outside (off + count + j) bounded (Or.inr (by omega))
      have currentBound : off + count + j < current.size := by omega
      rw [Array.getElem?_eq_getElem currentBound, Array.getElem?_eq_getElem bounded] at point
      simpa only [Array.getElem_extract] using Option.some.inj point
  have split : current.extract 0 off ++ current.extract off (off + count) ++
      current.extract (off + count) current.size = current := by
    rw [Array.extract_append_extract, Nat.zero_min,
      Nat.max_eq_right (by omega : off ≤ off + count), Array.extract_append_extract,
      Nat.zero_min, Nat.max_eq_right (by omega : off + count ≤ current.size), Array.extract_size]
  rw [first, last] at split
  exact split.symm

/-- The actual interval frame gives exact output bytes and a pure expected
Store heap. The actual heap retains its private decoder state and allocation
metadata; its old caller objects match that expected heap through Frame. -/
theorem output_frame_store
    {h after : Heap} {changed : Nat → Prop} {dest : BRef} {off made : Nat}
    {array : Array UInt8} (get : Space.get h dest = some array)
    (write : Space.ro h dest = false) (writeAfter : Space.ro after dest = false)
    (room : off + made ≤ array.size)
    (frame : BufferFrame h after changed [⟨.ref dest off, made⟩]) :
    ∃ output final expected,
      output.length = made ∧ Bytes after (.ref dest off) made output ∧
      Space.get after dest = some final ∧ final.size = array.size ∧
      final = array.extract 0 off ++ output.toArray ++ array.extract (off + made) array.size ∧
      Store h (.ref dest off) output expected ∧ Frame expected after changed := by
  obtain ⟨final, finalGet, size, untouched⟩ :=
    frame.2 ⟨.ref dest off, made⟩ (by simp) dest off array rfl get
  have outside : ∀ j, j < array.size → j < off ∨ off + made ≤ j → final[j]? = array[j]? := by
    intro j bounded separate
    apply untouched j bounded
    rintro ⟨region, member, start, pointer, lower, upper⟩
    have same : region = (⟨.ref dest off, made⟩ : Region) := by simpa using member
    subst region
    have sameOff : off = start := (Ptr.ref.inj pointer).2
    dsimp only at lower upper
    rcases separate with before | after <;> omega
  let output := (final.extract off (off + made)).toList
  have length : output.length = made := by
    simp only [output, Array.length_toList, Array.size_extract, size]
    omega
  have values : output = (final.toList.drop off).take made := by
    simp only [output, Array.toList_extract, List.extract, Nat.add_sub_cancel_left]
  have exactArray : final = array.extract 0 off ++ output.toArray ++ array.extract (off + made) array.size := by
    simpa only [output, Array.toArray_toList] using array_eq_prefix_slice_suffix array final off made size room outside
  let expected := Space.put h dest final
  have framed : Frame expected after changed := by
    have restored : Frame h (Space.put after dest array) changed := by
      simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using frame.1
    have reset := frame_reset_byte_view restored get write final
    rw [byte_view_put_put finalGet writeAfter, byte_view_put_self finalGet writeAfter] at reset
    exact reset
  refine ⟨output, final, expected, length,
    Or.inr ⟨dest, off, final, rfl, finalGet, by omega, values⟩,
    finalGet, size, exactArray, Or.inr ⟨dest, off, array, rfl, get, write, ?_, ?_⟩, framed⟩
  · simpa only [length] using room
  · change Space.put h dest final = _
    rw [length, ← exactArray]

/-- The same real returning loop has exact counts, cursor, output prefix,
final array slices and a pure expected Store heap. It retains exact bytes
and caller ranges of every object disjoint from the original output range.
Default allocation failures and partial output are included. -/
theorem loop_go_output_store
    (steps : Nat) (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    ∃ made output expected,
      remainingOutput stream next + made = remainingOutput z l ∧
      stream.next_out = inputAdvance z.next_out made ∧ output.length = made ∧
      Bytes after z.next_out made output ∧ CallerRange after (.tab b) z.next_out made true ∧
      BufferFrame h after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root)
        [⟨z.next_out, made⟩] ∧
      Store h z.next_out output expected ∧
      Frame expected after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root) ∧
      (∃ dest off array final, z.next_out = .ref dest off ∧
        Space.get h dest = some array ∧ Space.get after dest = some final ∧
        final.size = array.size ∧ off + made ≤ array.size ∧
        final = array.extract 0 off ++ output.toArray ++ array.extract (off + made) array.size) ∧
      (∀ p count xs write, CallerRange h (.tab b) p count write → Bytes h p count xs →
        Separate p count z.next_out (remainingOutput z l) →
        CallerRange after (.tab b) p count write ∧ Bytes after p count xs ∧
        Separate p count stream.next_out (remainingOutput stream next)) := by
  obtain ⟨made, count, cursor, frame⟩ :=
    loop_go_output_prefix steps h after b zs z stream s state l next invariant allocator ranges nonnull run current
  obtain ⟨dest, off, array, pointer, get, write, room⟩ := output_writable_view ranges nonnull
  have outputRange : CallerRange h (.tab b) (.ref dest off) (remainingOutput z l) true := by
    simpa only [pointer, remainingOutput] using ranges.2.1
  have frame' := frame
  rw [pointer] at frame'
  have writeAfter := (output_frame_readonly invariant.good get outputRange frame').trans write
  have madeRoom : off + made ≤ array.size := by omega
  obtain ⟨output, final, expected, length, observed, finalGet, size, exactArray, store, expectedFrame⟩ :=
    output_frame_store get write writeAfter madeRoom frame'
  obtain ⟨_ledger, owners⟩ := loop_go_resources steps h after b zs z stream s state l next
    invariant allocator ranges nonnull run current
  have rangeAfter := callerRange_after_bufferFrame invariant.good current outputRange get frame'
    (fun root live owner => (owners root live).mp owner)
  have observedRange : CallerRange after (.tab b) (.ref dest off) made true := by
    rcases rangeAfter with null | ⟨_, writable, outside⟩
    · cases null
    · exact Or.inr ⟨⟨output, observed⟩,
        fun _ => writable_prefix after (.ref dest off) (remainingOutput z l) made (writable rfl) (by omega), outside⟩
  refine ⟨made, output, expected, count, cursor, length, ?_, ?_, frame, ?_, expectedFrame,
    ⟨dest, off, array, final, pointer, get, finalGet, size, madeRoom, exactArray⟩, ?_⟩
  · simpa only [pointer] using observed
  · simpa only [pointer] using observedRange
  · simpa only [pointer] using store
  · intro p count xs write object bytes separate
    exact Zlib.Uncompr.Proof.Objects.loop_go_object steps h after b zs z stream s state l next
      p count xs write invariant allocator ranges nonnull object bytes separate run current

/-- Fixed-fuel source cdoWhile version of the exact prefix observation. -/
theorem loop_output_store
    (h after : Heap) (b zs : Nat) (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    ∃ made output expected,
      remainingOutput stream next + made = remainingOutput z l ∧
      stream.next_out = inputAdvance z.next_out made ∧ output.length = made ∧
      Bytes after z.next_out made output ∧ CallerRange after (.tab b) z.next_out made true ∧
      BufferFrame h after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root) [⟨z.next_out, made⟩] ∧
      Store h z.next_out output expected ∧
      Frame expected after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root) ∧
      (∃ dest off array final, z.next_out = .ref dest off ∧
        Space.get h dest = some array ∧ Space.get after dest = some final ∧
        final.size = array.size ∧ off + made ≤ array.size ∧
        final = array.extract 0 off ++ output.toArray ++ array.extract (off + made) array.size) ∧
      (∀ p count xs write, CallerRange h (.tab b) p count write → Bytes h p count xs →
        Separate p count z.next_out (remainingOutput z l) →
        CallerRange after (.tab b) p count write ∧ Bytes after p count xs ∧
        Separate p count stream.next_out (remainingOutput stream next)) :=
  loop_go_output_store C.fuel h after b zs z stream s state l next invariant allocator ranges nonnull run current

/-- The scalar-writeback theorem's same ordered Stores preserve the actual
observed output prefix, including same-allocation disjoint scalar slices. -/
theorem written_output_observation
    {core mid after : Heap} {b : Nat} {dest sourceLen destLen : BPtr}
    {output : List UInt8} {used made : UInt64}
    (observed : Bytes core dest output.length output)
    (range : CallerRange core (.tab b) dest output.length true)
    (sourceStore : Store core sourceLen (lengthBytes used) mid)
    (destStore : Store mid destLen (lengthBytes made) after)
    (ownership : ∀ root, StreamOwned after (.tab b) root ↔ StreamOwned core (.tab b) root)
    (sourceSeparate : Separate dest output.length sourceLen 8)
    (destSeparate : Separate dest output.length destLen 8) :
    Bytes after dest output.length output ∧ CallerRange after (.tab b) dest output.length true :=
  Zlib.Uncompr.Proof.Writeback.ordered_stores_keep_object sourceStore destStore ownership
    observed range sourceSeparate destSeparate

#print axioms output_frame_store
#print axioms loop_go_output_store
#print axioms loop_output_store
#print axioms written_output_observation
end Zlib.Uncompr.Proof.OutputPrefix
