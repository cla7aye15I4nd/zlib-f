import ZlibF.Proof.«inflate.c.local-fast-parser-distance-post»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-base-leaf-four-byte-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-root-loop-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-four-byte-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A root length-base leaf with sixteen held bits terminates the actual
one-pass `dolen` loop using at most four unread caller bytes. -/
theorem FastInputPacket.dolen_root_base_loop_four_byte_local_state
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
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 16 ≤ slow.bits.toNat)
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
    ∃ extra used consumed slowNext result after,
      extra < 2 ^ (lenCodes[index].op &&& 15).toNat ∧
      used ≤ 4 ∧ consumed ≤ 48 ∧
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.againL = false ∧ result.againD = false ∧
      FastInputPacket after slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result ∧
      DispatchBuffers after r slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: rest)) ∧
      (LocalFastDistancePost cutoff h after r zs z s slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result dest output j (lenCodes[index].val.toNat + extra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i ∧
         LocalStateJ after cutoff r zs
           { z with msg := .ref (.str i) 0 }
           { s with mode := BAD }) := by
  obtain ⟨extra, used, consumed, slowNext, result, after,
    extraBound, usedBound, consumedBound, run,
    againL, againD, nextPacket, nextBuffers, sizes,
    source, outcome⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dolen_base_leaf_four_byte_local_state packet) invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      (by omega) base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  exact ⟨extra, used, consumed, slowNext, result, after,
    extraBound, usedBound, consumedBound,
    dolen_loop_one run againL, againL, againD,
    nextPacket, nextBuffers, sizes, source, outcome⟩

end Zlib.Inflate.Local
