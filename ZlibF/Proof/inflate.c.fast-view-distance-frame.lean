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

/-- Rebase a continuing distance result's output frame to the entry range.
The hypotheses are all fields produced by the actual distance source proof. -/
theorem distance_outcome_normal_buffer_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {entry next : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (outcome : FastDistancePost before after r zs z s next bs
      result dest output j length ∨
      ∃ i, result.broke = true ∧
        after = badHeap before r zs z s i ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD })
    (hz : r.get before = some z)
    (hs : before.istates zs = some s)
    (notBroken : result.broke = false)
    (putEq : next.put = entry.put)
    (leftEq : next.left = entry.left) :
    BufferFrame before after (fun b => StreamRoot r b ∨ b = zs)
      [⟨entry.put, entry.left.toNat⟩] := by
  rcases outcome with post | ⟨i, broken, _, _⟩
  · have frame := post.buffer_frame hz hs
    simpa only [putEq, leftEq] using frame
  · rw [notBroken] at broken
    cases broken

/-- Either actual distance exit has a frame over its final ghost output range.
This includes the BAD exit, whose heap effect is confined to stream and state. -/
theorem distance_outcome_buffer_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {next : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (outcome : FastDistancePost before after r zs z s next bs
      result dest output j length ∨
      ∃ i, result.broke = true ∧
        after = badHeap before r zs z s i ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD })
    (hz : r.get before = some z)
    (hs : before.istates zs = some s) :
    BufferFrame before after (fun b => StreamRoot r b ∨ b = zs)
      [⟨next.put, next.left.toNat⟩] := by
  rcases outcome with post | ⟨i, _, heapEq, _⟩
  · exact post.buffer_frame hz hs
  · rw [heapEq]
    exact (badHeap_buffer_frame hz hs i
      [⟨next.put, next.left.toNat⟩]).1

#print axioms FastDistancePost.buffer_frame
#print axioms distance_outcome_normal_buffer_frame
#print axioms distance_outcome_buffer_frame

end Zlib.Inflate.Proofs
