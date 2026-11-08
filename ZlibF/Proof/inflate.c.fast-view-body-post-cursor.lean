import ZlibF.Proof.«inflate.c.fast-view-body-input-bridge»
import ZlibF.Proof.«inflate.c.fast-view-body-unified-six-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The public packet postcondition and six-byte cursor bound describe the same translated fast-body run. -/
theorem FastInputPacket.fast_body_view_post_with_cursor
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
    ∃ used consumed slowFinal result after zNext sNext array next,
      used ≤ 6 ∧ consumed ≤ 63 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      FastInputPacket after slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) result ∧
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
      result.in_ = slowFinal.next ∧
      result.bits = slowFinal.bits ∧
      slowFinal.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      ∃ pulled, pulled ≤ 6 ∧ result.in_ = inputAdvance l.in_ pulled := by
  obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      array, next, usedBound, consumedBound, bodyRun, finalPacket,
      finalInvariant, finalBuffers, sizes, trace, resultCursor,
      resultBits, bitBudget, outputOut, lower, upper, bytes, size⟩ :=
    packet.fast_body_view_post invariant buffers streamPtr statePtr mode
      whaveEq wsizeEq wnextEq windowEq lcodePtr codesGet safe lenMask
      dcodePtr distGet distSafe distMask bitsBound left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite outputSize current
      beginLe span guard
  obtain ⟨cursorResult, cursorAfter, pulled, pulledBound,
      cursorRun, cursor⟩ :=
    packet.fast_body_input_cursor_six invariant buffers streamPtr statePtr
      mode whaveEq wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask bitsBound left avail
      outPtr outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  have same : (result, after) = (cursorResult, cursorAfter) :=
    Except.ok.inj (bodyRun.symm.trans cursorRun)
  have resultEq : result = cursorResult := congrArg Prod.fst same
  subst cursorResult
  exact ⟨used, consumed, slowFinal, result, after, zNext, sNext,
    array, next, usedBound, consumedBound, bodyRun, finalPacket,
    finalInvariant, finalBuffers, sizes, trace, resultCursor,
    resultBits, bitBudget, outputOut, lower, upper, bytes, size,
    ⟨pulled, pulledBound, cursor⟩⟩

#print axioms FastInputPacket.fast_body_view_post_with_cursor
end Zlib.Inflate.Proofs
