import ZlibF.Proof.«inflate.c.fast-view-literal-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-root-literal-output-register-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A literal's one-pass actual length loop writes exactly through its output cursor. -/
theorem FastInputPacket.dolen_literal_loop_exact_frame
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
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
          .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j + 1 - oo⟩] := by
  obtain ⟨result, after, exactRun, out, frame⟩ :=
    packet.dolen_literal_exact_frame invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet outputWrite
      outputSize current guard
  obtain ⟨run, noAgain, _, _, _, _, _, _, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet outputWrite
      outputSize current guard
  have noAgainExact : result.againL = false := by
    rw [exactRun] at run
    cases run
    exact noAgain
  exact ⟨result, after, dolen_loop_one exactRun noAgainExact,
    out, frame⟩

#print axioms FastInputPacket.dolen_literal_loop_exact_frame

end Zlib.Inflate.Proofs
