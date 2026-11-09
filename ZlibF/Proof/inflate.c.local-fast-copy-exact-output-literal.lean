import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.slow-output-exact-frame»

/-! A literal's exact frame follows from its actual one-cell update.
No equality outside the written cell is supplied as a caller premise. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.literal_write_exact_output_frame
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (do
      store8 l.out value
      let out ← l.out.add 1
      pure { l with out }) h = .ok (result, after)) :
    result.out = .ref dest (j + 1) ∧
    BufferFrame h after (fun _ => False) [⟨.ref dest j, 1⟩] := by
  have actual := Zlib.Inflate.Local.FastInputPacket.literal_write_local_state packet invariant buffers
    left outPtr outputPtr outputGet outputWrite outputSize inside value
  dsimp only at actual
  obtain ⟨run, _, _, _, _, _, _, _⟩ := actual
  have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
  rcases same with ⟨rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  apply byte_view_segment_buffer_frame outputGet outputWrite (by simp)
  intro index outside
  have different : j ≠ index := by omega
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]

theorem FastInputPacket.literal_write_exact_output
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (do
      store8 l.out value
      let out ← l.out.add 1
      pure { l with out }) h = .ok (result, after)) :
    FastExactOutput h after r zs dest j result := by
  obtain ⟨out, frame⟩ := Zlib.Inflate.Local.FastInputPacket.literal_write_exact_output_frame packet
    invariant buffers left outPtr outputPtr outputGet outputWrite outputSize inside value observed
  refine ⟨j + 1, out, by omega, ?_⟩
  have permitted := bufferFrame_weaken (wider := fun b => StreamRoot r b ∨ b = zs)
    (fun _ impossible => False.elim impossible) frame
  simpa only [Nat.add_sub_cancel_left] using permitted

#print axioms FastInputPacket.literal_write_exact_output_frame
#print axioms FastInputPacket.literal_write_exact_output
end Zlib.Inflate.Local
