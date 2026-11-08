import ZlibF.Proof.«inflate.c.fast-view-distance-post»
import ZlibF.Proof.«inflate.c.fast-view-copy-match-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Both branches of the actual distance decoder's recorded postcondition
respect the caller output region. The diagnostic branch writes no bytes. -/
theorem FastDistancePost.buffer_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {result : Zlib.Inffast.L} {dest : BRef}
    {output : Array UInt8} {j length : Nat}
    (post : FastDistancePost before after r zs z s slow bs
      result dest output j length)
    (hz : r.get before = some z)
    (hs : before.istates zs = some s) :
    BufferFrame before after (fun b => StreamRoot r b ∨ b = zs)
      [⟨slow.put, slow.left.toNat⟩] := by
  rcases post with ⟨_, _, _, bad | copied⟩
  · rcases bad with ⟨i, _, heapEq, _, _, _⟩
    rw [heapEq]
    exact (badHeap_buffer_frame hz hs i
      [⟨slow.put, slow.left.toNat⟩]).1
  · rcases copied with ⟨_, _, _, _, _, _, _, frame⟩
    exact bufferFrame_weaken (fun _ impossible => False.elim impossible) frame

#print axioms FastDistancePost.buffer_frame

end Zlib.Inflate.Proofs
