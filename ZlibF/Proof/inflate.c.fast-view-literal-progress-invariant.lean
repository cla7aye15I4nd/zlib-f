import ZlibF.Proof.«inflate.c.fast-view-distance-progress-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- On a literal root entry, the actual one-pass `dolen` loop advances the
output pointer exactly once. -/
theorem FastInputPacket.dolen_root_literal_output_advance
    {h after : Heap} {slow : IL} {bs : List UInt8}
    {l result : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (run : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after)) :
    result.out = .ref dest (j + 1) := by
  obtain ⟨literalRun, noAgain, _, _, _, _, _, _, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard
  have loopRun := dolen_loop_one literalRun noAgain
  have eq := Except.ok.inj (loopRun.symm.trans run)
  have same := (Prod.mk.inj eq).1
  cases same
  rfl

/-- The second literal pass of a linked `dolen` loop advances the output
pointer exactly once after the first pass leaves the output untouched. -/
theorem FastInputPacket.dolen_linked_literal_output_advance
    {h after : Heap} {slow : IL} {bs : List UInt8}
    {l linked result : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs linked)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (firstRun : C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h))
    (againL : linked.againL = true)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : linked.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : linked.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt linked.out c.end_) h = .ok (true, h))
    (run : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after)) :
    result.out = .ref dest (j + 1) := by
  obtain ⟨secondRun, noAgain, _, _, _, _, _, _, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard
  let expected : Zlib.Inffast.L := { linked with
    againL := false,
    op := lenCodes[index].op.toUInt32,
    hold := linked.hold >>>
      lenCodes[index].bits.toUInt32.toUInt64,
    bits := linked.bits - lenCodes[index].bits.toUInt32,
    out := .ref dest (j + 1) }
  have cond2 : C.run (pure (expected.againL, expected))
      (Space.put h dest (output.set! j lenCodes[index].val.toUInt8)) =
      .ok ((false, expected),
        Space.put h dest (output.set! j lenCodes[index].val.toUInt8)) := by
    simp only [expected, C.run, pure]
  have loopRun := Zlib.Inffast.Proofs.cdoWhile_two
    (body := Zlib.Inffast.dolen c)
    (cond := fun q => pure (q.againL, q)) firstRun
    (by simp only [againL, C.run, pure] :
      C.run (pure (linked.againL, linked)) h =
        .ok ((true, linked), h))
    secondRun cond2
  have same := (Prod.mk.inj (Except.ok.inj (loopRun.symm.trans run))).1
  rw [← same]

end Zlib.Inflate.Proofs
