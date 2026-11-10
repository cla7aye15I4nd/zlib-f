import ZlibF.Proof.«inflate.c.fast-view-body-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-rank-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast body runs either initial-refill branch, decodes a safe
root entry, and strictly decreases remaining output space unless it breaks. -/
theorem FastInputPacket.fast_body_rank_frame_default_state
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
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
    ∃ used consumed slowFinal result after zNext sNext,
      used ≤ 6 ∧ consumed ≤ 63 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        result ∧
      DefaultStateJ after r zs zNext sNext ∧
      DispatchBuffers after r slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) ∧
      (result.broke = true ∨
        ∃ next, result.out = .ref dest next ∧
          next ≤ oo + slow.left.toNat ∧
          oo + slow.left.toNat - next <
            oo + slow.left.toNat - j) ∧
      (result.broke = false →
        slowFinal.put = slow.put ∧
        slowFinal.left = slow.left ∧
        slowFinal.out_ = slow.out_ ∧
        slowFinal.next = inputAdvance slow.next used) := by
  obtain ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes,
    source, frameAfter⟩ :=
    packet.fast_body_frame_default_state
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  obtain ⟨_, _, _, result₂, after₂, _, _, _, _, run₂,
    _, _, _, _, _, progress⟩ :=
    packet.fast_body_bounded_progress_default_state
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have same : result₂ = result ∧ after₂ = after := by
    rw [run] at run₂
    cases run₂
    exact ⟨rfl, rfl⟩
  rw [same.1] at progress
  have rank := fast_body_output_measure_decreases outPtr
    endPtr outputGet outputSize current avail guard progress
  exact ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes,
    source, rank, frameAfter⟩

end Zlib.Inflate.Proofs
