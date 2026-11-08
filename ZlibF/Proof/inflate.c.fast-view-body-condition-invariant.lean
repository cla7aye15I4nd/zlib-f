import ZlibF.Proof.«inflate.c.fast-view-loop-guard-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-rank-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast body runs either initial-refill branch, decodes a safe
root entry, and strictly decreases remaining output space unless it breaks. -/
theorem FastInputPacket.fast_body_condition_default_state
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
            next + 258 ≤ oo + slow.left.toNat) := by
  obtain ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes,
    source, rank, frameAfter⟩ :=
    packet.fast_body_rank_cursor_default_state
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq lcodePtr codesGet safe
      lenMask dcodePtr distGet distSafe distMask bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
      nextPtr lastPtr
  refine ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, run,
    packetAfter, stateAfter, buffersAfter, sizes,
    source, rank, frameAfter, ?_⟩
  by_cases broke : result.broke = true
  · refine ⟨false, fast_loop_cond_broken broke, ?_⟩
    intro impossible
    cases impossible
  · have notBroken : result.broke = false := by
      cases flag : result.broke <;> simp_all
    rcases rank with bad | ⟨next, outEq, within, decreases⟩
    · rw [notBroken] at bad
      cases bad
    obtain ⟨putFrame, leftFrame, _, cursorFrame,
      _, lastFrame⟩ := frameAfter notBroken
    have nextFrame : slowFinal.next =
        .ref inputRef (inputOff + used) := by
      rw [cursorFrame, nextPtr]
      rfl
    have putPtr : slowFinal.put = .ref dest oo := by
      rw [putFrame]
      exact outputPtr
    have endAfter : c.end_ = .ref dest
        (oo + slowFinal.left.toNat - 257) := by
      simpa only [leftFrame] using endPtr
    have availAfter : 258 ≤ slowFinal.left.toNat := by
      rw [leftFrame]
      exact avail
    have withinAfter : next ≤ oo + slowFinal.left.toNat := by
      rwa [leftFrame]
    have cond := packetAfter.fast_loop_cond_from_buffers
      buffersAfter notBroken nextFrame lastFrame outEq
      putPtr endAfter withinAfter availAfter
    let keepGoing : Bool :=
      decide (6 ≤ slowFinal.have_.toNat) &&
        decide (next + 258 ≤ oo + slowFinal.left.toNat)
    refine ⟨keepGoing, cond, ?_⟩
    intro yes
    have both :
        decide (6 ≤ slowFinal.have_.toNat) = true ∧
        decide (next + 258 ≤ oo + slowFinal.left.toNat) = true := by
      simpa only [keepGoing, Bool.and_eq_true] using yes
    have inputMargin : 6 ≤ slowFinal.have_.toNat := by
      simpa using both.1
    have outputMargin : next + 258 ≤ oo + slow.left.toNat := by
      have bound : next + 258 ≤ oo + slowFinal.left.toNat := by
        simpa using both.2
      rwa [leftFrame] at bound
    exact ⟨notBroken, inputMargin, next, outEq, outputMargin⟩

end Zlib.Inflate.Proofs
