import ZlibF.Proof.«inflate.c.fast-view-copy-match-frame»
import ZlibF.Proof.«inflate.c.fast-view-terminal-frame»
import ZlibF.Proof.«inflate.c.fast-view-distance-post»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Source effects that can leave one fast decoder body. The first case
allows a caller output write; BAD and TYPE update only stream records.
The alternatives are established by source branch proofs, never assumed
at a public call boundary. -/
def FastOutputEffect (before after : Heap) (r : ZStreamRef)
    (zs : Nat) (z : ZStream) (s : InflateState)
    (slow : IL) (dest : BRef) : Prop :=
  (∃ array, after = Space.put before dest array ∧
    BufferFrame before after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩]) ∨
  (∃ i, after = badHeap before r zs z s i) ∨
  after = setI before zs { s with mode := TYPE }

theorem FastOutputEffect.buffer_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {dest : BRef}
    (effect : FastOutputEffect before after r zs z s slow dest)
    (hz : r.get before = some z)
    (hs : before.istates zs = some s) :
    BufferFrame before after (fun b => StreamRoot r b ∨ b = zs)
      [⟨slow.put, slow.left.toNat⟩] := by
  rcases effect with ⟨_, _, frame⟩ | ⟨i, heapEq⟩ | heapEq
  · exact bufferFrame_weaken (fun _ impossible => False.elim impossible) frame
  · rw [heapEq]
    exact (badHeap_buffer_frame hz hs i
      [⟨slow.put, slow.left.toNat⟩]).1
  · rw [heapEq]
    exact (fast_terminal_buffer_frame hz hs
      [⟨slow.put, slow.left.toNat⟩]).1

/-- The actual distance post retains the precise output-or-diagnostic
heap effect, including valid copying that enters with `broke=true`. -/
theorem FastDistancePost.output_effect
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (post : FastDistancePost before after r zs z s slow bs
      result dest output j length) :
    FastOutputEffect before after r zs z s slow dest := by
  rcases post with ⟨_, _, _, bad | copied⟩
  · rcases bad with ⟨i, _, heapEq, _, _, _⟩
    exact Or.inr (Or.inl ⟨i, by simpa only [badHeap] using heapEq⟩)
  · rcases copied with ⟨array, _, _, _, _, _, heapEq, frame⟩
    exact Or.inl ⟨array, heapEq, frame⟩

theorem distance_outcome_output_effect
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (outcome : FastDistancePost before after r zs z s slow bs
      result dest output j length ∨
      ∃ i, result.broke = true ∧
        after = badHeap before r zs z s i ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD }) :
    FastOutputEffect before after r zs z s slow dest := by
  rcases outcome with post | ⟨i, _, heapEq, _⟩
  · exact post.output_effect
  · exact Or.inr (Or.inl ⟨i, heapEq⟩)

#print axioms FastOutputEffect.buffer_frame
#print axioms FastDistancePost.output_effect
#print axioms distance_outcome_output_effect

end Zlib.Inflate.Proofs
