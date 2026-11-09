import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-parser-dolen-base-leaf-four-byte-invariant»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-terminals»
import ZlibF.Proof.«inflate.c.fast-view-dolen-classify-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dolen_leaf_four_byte_execution_exact_output
    {h : Heap} {cutoff : Nat} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    {priorBits : Nat} (leaf : LenLeaf priorBits lenCodes[index])
    (room : 1 + lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after, C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.againL = false ∧ FastExactOutput h after r zs dest j result := by
  have width : lenCodes[index].bits.toNat ≤ 15 := by have bound := leaf.1; omega
  rcases (len_leaf_source_cases leaf).2 with literal | base | terminal | invalid
  · obtain ⟨run, againL, _⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_literal_local_state packet invariant buffers herePtr lenGet indexBound codeFits width literal
        left avail outPtr outputPtr endPtr outputGet outputWrite outputSize current guard
    refine ⟨_, _, run, againL, ?_⟩
    have effect := Zlib.Inflate.Local.FastInputPacket.dolen_literal_exact_output packet invariant buffers herePtr lenGet indexBound codeFits width literal
        left avail outPtr outputPtr endPtr outputGet outputWrite outputSize current guard run
    exact effect
  · obtain ⟨extra, used, consumed, slowNext, result, after, _, _, _, run, againL, _⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_base_leaf_four_byte_local_state packet invariant buffers streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr lenGet indexBound codeFits width room base.1 base.2.1 ⟨base.2.2.1, base.2.2.2⟩
        dcodePtr distGet distSafe distMask bitsBound left avail outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe span guard
    refine ⟨result, after, run, againL, ?_⟩
    exact Zlib.Inflate.Local.FastInputPacket.dolen_base_leaf_four_byte_exact_output packet invariant buffers streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr lenGet indexBound codeFits width room base.1 base.2.1 ⟨base.2.2.1, base.2.2.2⟩
        dcodePtr distGet distSafe distMask bitsBound left avail outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe span guard run
  · obtain ⟨result, slowNext, run, _, againL, _⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_end_leaf_local_state packet invariant buffers statePtr mode herePtr lenGet indexBound codeFits width
        terminal.1 terminal.2.1 terminal.2.2.1 terminal.2.2.2
    refine ⟨result, _, run, againL, ?_⟩
    have effect := Zlib.Inflate.Local.FastInputPacket.dolen_end_leaf_exact_output packet invariant buffers statePtr mode herePtr lenGet indexBound codeFits width
        terminal.1 terminal.2.1 terminal.2.2.1 terminal.2.2.2 outPtr run
    exact effect
  · obtain ⟨i, after, result, slowNext, run, _, _, againL, _⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dolen_invalid_leaf_local_state packet invariant buffers streamPtr statePtr herePtr lenGet indexBound codeFits width
        invalid.1 invalid.2.1 invalid.2.2.1 invalid.2.2.2
    refine ⟨result, after, run, againL, ?_⟩
    have effect := Zlib.Inflate.Local.FastInputPacket.dolen_invalid_leaf_exact_output packet invariant buffers streamPtr statePtr herePtr lenGet indexBound codeFits width
        invalid.1 invalid.2.1 invalid.2.2.1 invalid.2.2.2 outPtr run
    exact effect

end Zlib.Inflate.Local
