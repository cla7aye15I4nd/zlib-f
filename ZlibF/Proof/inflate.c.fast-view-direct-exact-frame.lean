import ZlibF.Proof.«inflate.c.fast-view-direct-invariant»
import ZlibF.Proof.«inflate.c.fast-view-literal-exact-frame»
import ZlibF.Proof.«inffast.c.frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The direct match branch's sequential overlapping copy changes no
output byte beyond its final cursor. -/
theorem FastInputPacket.copyMatch_direct_exact_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (direct : ¬ l.dist > l.op)
    (distance : l.dist.toNat ≤ j)
    (length : 3 ≤ l.len.toNat)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j + l.len.toNat - oo⟩] := by
  obtain ⟨result, after, run, _, _, _, _, resultEq,
    nextGet, _, _, broad⟩ :=
    packet.copyMatch_direct_default_state invariant buffers
      left direct distance length outPtr outputPtr outputGet
      outputWrite outputSize outputRoom
  let next : Array UInt8 := Zlib.Inffast.Proofs.cpyN
    l.len.toNat (j - l.dist.toNat) j output
  have exact : BufferFrame h after
      (fun b => StreamRoot r b ∨ b = zs)
      [⟨.ref dest oo, j + l.len.toNat - oo⟩] := by
    have wide : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨.ref dest oo, slow.left.toNat⟩] := by
      simpa only [outputPtr] using
        bufferFrame_weaken (fun _ impossible => False.elim impossible)
          broad
    apply BufferFrame.singleton_narrow wide outputGet nextGet
    intro p bound outside
    apply Zlib.Inffast.Proofs.cpyN_frame
    omega
  refine ⟨result, after, run, ?_, ?_⟩
  · rw [resultEq]
  · simpa only [outputPtr] using exact

#print axioms FastInputPacket.copyMatch_direct_exact_frame

end Zlib.Inflate.Proofs
