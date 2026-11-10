import ZlibF.Proof.«inflate.c.fast-eob-twopull-body-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- Real fast-body EOB output cursor for both root/link table choices and
both initial refill choices. This result is independent of the byte-view
object identities. -/
theorem FastInputPacket.fast_body_eob_output_cursor
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {tail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail))
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth used : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth used lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat)
    {rest : List Bool}
    (decoded : decodeSym lens (stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: tail)) =
      some (256, rest)) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.out = l.out := by
  by_cases small : slow.bits.toNat < 15
  · exact packet.fast_body_two_pull_eob_output_cursor invariant
      buffers small statePtr mode lcodePtr codesGet safe meaning
      mask outPtr outputGet cursorBound decoded
  · have held : ¬ l.bits < 15 := by
      intro smaller
      have bits := packet.bits
      rw [bits] at smaller
      have nat : slow.bits.toNat < 15 := by
        simpa using UInt32.lt_iff_toNat_lt.mp smaller
      exact small nat
    have rootFits : rootWidth ≤ slow.bits.toNat := by
      have width := safe.1
      omega
    exact packet.fast_body_no_pull_eob_output_cursor invariant
      buffers held statePtr mode lcodePtr codesGet safe meaning
      mask rootFits outPtr outputGet cursorBound decoded

#print axioms FastInputPacket.fast_body_eob_output_cursor
end Zlib.Inflate.Proofs
