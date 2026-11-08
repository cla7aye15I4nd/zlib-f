import ZlibF.Proof.«inflate.c.fast-view-match-invariant»
import ZlibF.Proof.«inflate.c.fast-view-bad-data-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem bufferFrame_weaken
    {before after : Heap} {changed wider : Nat → Prop}
    {regions : List Region}
    (subset : ∀ b, changed b → wider b)
    (frame : BufferFrame before after changed regions) :
    BufferFrame before after wider regions := by
  rcases frame with ⟨⟨static, allocOk, garbage, nextBlk, nalloc, outside⟩, bytes⟩
  refine ⟨⟨static, allocOk, garbage, nextBlk, nalloc, ?_⟩, bytes⟩
  intro b live unchanged
  exact outside b live (fun changed => unchanged (subset b changed))

/-- Actual copyMatch writes only inside the caller output range, including
the invalid-distance branch, which writes a diagnostic but no output byte. -/
theorem FastInputPacket.copyMatch_buffer_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op →
      ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, slow.left.toNat⟩] := by
  obtain ⟨result, after, run, _, _, _, _, _, branches⟩ :=
    packet.copyMatch_default_state invariant buffers streamPtr statePtr
      left length whaveBound wnextBound wsizeBound outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced windowData
  refine ⟨result, after, run, ?_⟩
  rcases branches with ⟨i, _, heapEq, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, heapEq, frame⟩
  · rw [heapEq]
    exact (badHeap_buffer_frame invariant.good.live.hz
      invariant.good.live.hs i [⟨slow.put, slow.left.toNat⟩]).1
  · exact bufferFrame_weaken (fun _ changed => False.elim changed) frame

#print axioms FastInputPacket.copyMatch_buffer_frame

end Zlib.Inflate.Proofs
