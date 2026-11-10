import ZlibF.Proof.«uncompr.c.output-store»
import ZlibF.Proof.«uncompr.c.local-output-prefix»
import ZlibF.Proof.«uncompr.c.local-loop-resources»

namespace Zlib.Uncompr.Proof.LocalOutputPrefix
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.OutputPrefix
set_option autoImplicit false

/-- The same real returning loop has exact counts, cursor, output prefix,
final array slices and a pure expected Store heap. It retains exact bytes
and caller ranges of every object disjoint from the original output range.
Default allocation failures and partial output are included. -/
theorem loop_go_output_store
    (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) :
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
    LocalOutputPrefix.loop_go_output_prefix steps h after cutoff b zs z stream s state l next invariant allocator ranges nonnull run current.good
  obtain ⟨dest, off, array, pointer, get, write, room⟩ := output_writable_view ranges nonnull
  have outputRange : CallerRange h (.tab b) (.ref dest off) (remainingOutput z l) true := by
    simpa only [pointer, remainingOutput] using ranges.2.1
  have frame' := frame
  rw [pointer] at frame'
  have writeAfter := (LocalOutputPrefix.output_frame_readonly invariant get outputRange frame').trans write
  have madeRoom : off + made ≤ array.size := by omega
  obtain ⟨output, final, expected, length, observed, finalGet, size, exactArray, store, expectedFrame⟩ :=
    output_frame_store get write writeAfter madeRoom frame'
  obtain ⟨_ledger, owners⟩ := LocalLoop.loop_go_resources steps h after cutoff b zs z stream s state l next
    invariant allocator ranges nonnull run current.good
  have outputStable : C.LibcBorrow.BorrowStable h after dest := by
    cases dest with
    | str i => simp [Space.ro] at write
    | _ => trivial
  have rangeAfter := LocalPostRanges.callerRange_after_bufferFrame invariant current outputRange get frame'
    (fun root live owner => (owners root live).mp owner)
    (fun {ref off input} pointer _ => by cases pointer; exact outputStable)
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
    exact LocalObjects.loop_go_object steps h after cutoff b zs z stream s state l next
      p count xs write invariant allocator ranges nonnull object bytes separate run current

/-- Fixed-fuel source cdoWhile version of the exact prefix observation. -/
theorem loop_output_store
    (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) :
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
  loop_go_output_store C.fuel h after cutoff b zs z stream s state l next invariant allocator ranges nonnull run current


#print axioms loop_go_output_store
#print axioms loop_output_store
end Zlib.Uncompr.Proof.LocalOutputPrefix
