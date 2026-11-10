import ZlibF.Proof.«inflate.c.fast-view-body-condition-heap-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-bits-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast body runs either initial-refill branch, decodes a safe
root entry, and strictly decreases remaining output space unless it breaks. -/
theorem FastInputPacket.fast_body_condition_heap_bits_default_state
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {inputRef : BRef} {inputOff : Nat}
    (nextPtr : slow.next = .ref inputRef inputOff)
    (lastPtr : c.last = .ref inputRef
      (inputOff + slow.have_.toNat - 5)) :
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
        slowFinal.next = inputAdvance slow.next used ∧
        slowFinal.have_.toNat + used = slow.have_.toNat ∧
        c.last = .ref inputRef
          (inputOff + used + slowFinal.have_.toNat - 5)) ∧
      (result.broke = false →
        ∃ array, after = Space.put h dest array ∧
          zNext = z ∧ sNext = s) ∧
      ∃ keepGoing,
        C.run (do
          if result.broke then pure (false, result)
          else if ← Ptr.lt result.in_ c.last then
            pure (← Ptr.lt result.out c.end_, result)
          else pure (false, result)) after =
          .ok ((keepGoing, result), after) ∧
        (keepGoing = true →
          result.broke = false ∧
          6 ≤ slowFinal.have_.toNat ∧
          ∃ next, result.out = .ref dest next ∧
            next + 258 ≤ oo + slow.left.toNat) ∧
        (keepGoing = true → slowFinal.bits.toNat ≤ 30) := by
  obtain ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes, source,
    rank, frameAfter, heapAfter, keepGoing, condRun,
    continuing⟩ :=
    packet.fast_body_condition_heap_default_state
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
      nextPtr lastPtr
  obtain ⟨_, slowBits, resultBits, afterBits, runBits,
    packetBits, boundBits⟩ :=
    packet.fast_body_bits_default_state invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet
      distSafe distMask bitsBound left avail outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
  rw [run] at runBits
  cases runBits
  have sameBits : slowFinal.bits = slowBits.bits :=
    packetAfter.bits.symm.trans packetBits.bits
  refine ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes, source,
    rank, frameAfter, heapAfter, keepGoing, condRun,
    continuing, ?_⟩
  intro yes
  rw [sameBits]
  exact boundBits (continuing yes).1

end Zlib.Inflate.Proofs
