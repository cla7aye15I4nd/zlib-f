import ZlibF.Proof.«inflate.c.fast-view-dolen-root-loop-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A root literal keeps the input and caller output registers fixed while
writing exactly one byte and advancing the fast output cursor. -/
theorem FastInputPacket.dolen_root_literal_frame_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ slowNext result after,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.againL = false ∧
      FastInputPacket after slowNext bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slowNext bs ∧
      ByteViewSizes h after ∧
      stream slowNext bs =
        (stream slow bs).drop lenCodes[index].bits.toNat ∧
      Space.get after dest = some
        (output.set! j lenCodes[index].val.toUInt8) ∧
      Space.ro after dest = false ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] ∧
      slowNext.put = slow.put ∧
      slowNext.left = slow.left ∧
      slowNext.next = slow.next ∧
      slowNext.have_ = slow.have_ ∧
      result.in_ = l.in_ := by
  let entry : Code := lenCodes[index]
  let count : UInt32 := entry.bits.toUInt32
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let result : Zlib.Inffast.L := { l with
    againL := false,
    op := entry.op.toUInt32,
    hold := l.hold >>> count.toUInt64,
    bits := l.bits - count,
    out := .ref dest (j + 1) }
  let after := Space.put h dest
    (output.set! j entry.val.toUInt8)
  obtain ⟨run, noAgain, nextPacket, nextState,
    nextBuffers, sizes, source, outputAfter,
    writable, frame⟩ :=
    packet.dolen_literal_default_state invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard
  exact ⟨slowNext, result, after,
    dolen_loop_one run noAgain, noAgain,
    nextPacket, nextState, nextBuffers, sizes,
    source, outputAfter, writable, frame,
    rfl, rfl, rfl, rfl, rfl⟩

end Zlib.Inflate.Proofs
