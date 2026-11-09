import ZlibF.Proof.«uncompr.c.local-loop-iteration»
import ZlibF.Proof.«uncompr.c.loop-safe»

namespace Zlib.Uncompr.Proof.LocalPostRanges
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers
set_option autoImplicit false

private theorem byteRoot_live {h : Heap} {ref : BRef} {off b : Nat} {a : Array UInt8}
    (get : Space.get h ref = some a) (root : ByteRoot (.ref ref off) b) : h.live b := by
  cases ref with
  | blk i =>
    change b = i at root
    subst b
    exact Or.inl (by simp [show h.bytes i = some a from get])
  | dstate_depth i =>
    change b = i at root
    subst b
    cases hg : h.dstates i with
    | none => simp [Space.get, hg] at get
    | some state => simp [Heap.live, hg]
  | str i => cases root
  | st_dist_code => cases root
  | st_length_code => cases root

private theorem byte_put_heap_ro (h : Heap) (ref : BRef) (a : Array UInt8) :
    (Space.put h ref a).ro = h.ro := by
  cases ref <;> simp [Space.put]
  split <;> rfl

private theorem callerRange_read {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

/-- An exact output frame preserves every caller object's capacity and writability.
Ownership of old live objects is kept explicit, so allocating a new window is included. -/
theorem callerRange_after_bufferFrame
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {p : BPtr} {n : Nat} {write : Bool}
    {dest : BRef} {outOffset made : Nat} {outArray : Array UInt8}
    (invariant : LocalStateJ h cutoff r zs z s) (current : LocalStateJ after cutoff r zs stream state)
    (range : CallerRange h r p n write) (outputGet : Space.get h dest = some outArray)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest outOffset, made⟩])
    (oldOwned : ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b) :
    CallerRange after r p n write := by
  rcases range with null | ⟨⟨xs, readable⟩, writable, unowned⟩
  · exact Or.inl null
  · rcases readable with null | ⟨source, off, array, pointer, get, room, values⟩
    · exact Or.inl null.1
    · subst p
      have oldRange : CallerRange h r (.ref source off) n false :=
        Or.inr ⟨⟨xs, Or.inr ⟨source, off, array, rfl, get, room, values⟩⟩, by simp, unowned⟩
      have outside := fun b root => Zlib.Inflate.Local.caller_byte_root_outside invariant get oldRange (b := b) root
      obtain ⟨newArray, newGet, sameSize⟩ : ∃ a', Space.get after source = some a' ∧ a'.size = array.size := by
        by_cases shared : source = dest
        · subst source
          obtain ⟨a', hget, hsize, _⟩ := frame.2 ⟨.ref dest outOffset, made⟩ (by simp) dest outOffset array rfl get
          exact ⟨a', hget, hsize⟩
        · exact ⟨array, BufferFrame.other_view_get frame get outputGet outside shared, rfl⟩
      have roKept : Space.ro after source = Space.ro h source := by
        cases source with
        | blk b =>
          have live := byteRoot_live get (show ByteRoot (.ref (.blk b) off) b from rfl)
          have slot := frame.1.2.2.2.2.2 b live (outside b rfl)
          have restoreRo : (restoreRegions h after [⟨.ref dest outOffset, made⟩]).ro = after.ro := by
            simpa [restoreRegions, outputGet] using byte_put_heap_ro after dest outArray
          change after.ro b = h.ro b
          rw [← restoreRo]
          exact slot.2.2.2.2.2.2.2
        | str i => rfl
        | dstate_depth i => rfl
        | st_dist_code => rfl
        | st_length_code => rfl
      refine Or.inr ⟨⟨(newArray.toList.drop off).take n,
        Or.inr ⟨source, off, newArray, rfl, newGet, by omega, rfl⟩⟩, ?_, ?_⟩
      · intro writing
        rcases writable writing with null | ⟨ref, offset, a, ptr, getA, ro, _⟩
        · cases null.1
        · cases ptr
          exact Or.inr ⟨source, off, newArray, rfl, newGet, roKept.trans ro, by omega⟩
      · intro b root owned
        apply unowned b root
        rw [invariant.good.streamOwned_iff]
        exact oldOwned b (byteRoot_live get root) ((current.good.streamOwned_iff b).mp owned)


#print axioms callerRange_after_bufferFrame
end Zlib.Uncompr.Proof.LocalPostRanges
