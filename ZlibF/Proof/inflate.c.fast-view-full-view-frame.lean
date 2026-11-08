import ZlibF.Proof.«inflate.c.fast-view-output-effect»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Replacing a writable byte view by an equally sized array changes no
object outside that entire view. This is a coarse frame used before the
source proof narrows writes to the caller's output interval. -/
theorem byte_view_full_buffer_frame
    {h : Heap} {dest : BRef} {old array : Array UInt8}
    (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (size : array.size = old.size) :
    BufferFrame h (Space.put h dest array) (fun _ => False)
      [⟨.ref dest 0, old.size⟩] := by
  have restored : restoreRegions h (Space.put h dest array)
      [⟨.ref dest 0, old.size⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil,
      get, byte_view_put_put get write array old,
      byte_view_put_self get write]
  refine ⟨?_, ?_⟩
  · rw [restored]
    simp only [Frame, Nat.le_refl, true_and]
    intro b live unchanged
    repeat' constructor <;> rfl
  · intro region member ref off beforeArray pointer getRef
    simp only [List.mem_singleton] at member
    subst region
    cases pointer
    have beforeEq : beforeArray = old := by
      rw [get] at getRef
      cases getRef
      rfl
    subst beforeArray
    refine ⟨array, byte_view_get_put get write array, size, ?_⟩
    intro j within outside
    exfalso
    apply outside
    exact ⟨⟨.ref dest 0, old.size⟩, by simp,
      0, rfl, Nat.zero_le _, by simpa using within⟩

/-- The three actual body effects share a coarse frame over the whole
writable output view. This conclusion needs no equality between the
body's final ghost `slow.put` and the entry pointer. -/
theorem FastOutputEffect.full_view_buffer_frame
    {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {dest : BRef}
    {old : Array UInt8}
    (effect : FastOutputEffect h after r zs z s slow dest)
    (sizes : ByteViewSizes h after)
    (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (hz : r.get h = some z)
    (hs : h.istates zs = some s) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
      [⟨.ref dest 0, old.size⟩] := by
  rcases effect with ⟨array, heapEq, _⟩ | ⟨i, heapEq⟩ | heapEq
  · have current := sizes.view get
    obtain ⟨arrayNext, getNext, sameSize⟩ := current
    rw [heapEq, byte_view_get_put get write array] at getNext
    cases getNext
    rw [heapEq]
    exact bufferFrame_weaken
      (fun _ impossible => False.elim impossible)
      (byte_view_full_buffer_frame get write sameSize)
  · rw [heapEq]
    exact (badHeap_buffer_frame hz hs i
      [⟨.ref dest 0, old.size⟩]).1
  · rw [heapEq]
    exact (fast_terminal_buffer_frame hz hs
      [⟨.ref dest 0, old.size⟩]).1

#print axioms byte_view_full_buffer_frame
#print axioms FastOutputEffect.full_view_buffer_frame

end Zlib.Inflate.Proofs
