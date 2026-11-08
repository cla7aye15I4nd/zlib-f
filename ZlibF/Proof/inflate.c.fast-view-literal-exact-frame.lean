import ZlibF.Proof.«inflate.c.fast-view-dolen-literal-invariant»
import ZlibF.Proof.«inflate.c.fast-view-exact-frame-bridge»
import ZlibF.Proof.«inflate.c.fast-view-copy-match-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual literal branch changes only the produced output prefix,
ending at the advanced `out` cursor. -/
theorem FastInputPacket.dolen_literal_exact_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j + 1 - oo⟩] := by
  have source := packet.dolen_literal_default_state invariant buffers
    herePtr lenGet indexBound codeFits codeWidth literal
    left avail outPtr outputPtr endPtr outputGet outputWrite
    outputSize current guard
  dsimp only at source
  obtain ⟨run, _, _, _, _, _, _, nextGet, _, broad⟩ := source
  let entry : Code := lenCodes[index]
  let result : Zlib.Inffast.L := { l with
    againL := false, op := entry.op.toUInt32,
    hold := l.hold >>> entry.bits.toUInt32.toUInt64,
    bits := l.bits - entry.bits.toUInt32,
    out := .ref dest (j + 1) }
  let after := Space.put h dest (output.set! j entry.val.toUInt8)
  have exact : BufferFrame h after
      (fun b => StreamRoot r b ∨ b = zs)
      [⟨slow.put, j + 1 - oo⟩] := by
    rw [outputPtr]
    have wide : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨.ref dest oo, slow.left.toNat⟩] := by
      simpa only [outputPtr] using
        bufferFrame_weaken (fun _ impossible => False.elim impossible)
          broad
    apply BufferFrame.singleton_narrow wide outputGet nextGet
    intro p bound outside
    have notSame : j ≠ p := by omega
    simp [Array.set!, notSame]
  exact ⟨result, after, run, rfl, by simpa only [outputPtr] using exact⟩

#print axioms FastInputPacket.dolen_literal_exact_frame

end Zlib.Inflate.Proofs
