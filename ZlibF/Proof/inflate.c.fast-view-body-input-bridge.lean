import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»
import ZlibF.Proof.«inflate.c.fast-view-body-pull-branch-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A consumed prefix of the bit stream bounds the live bits by the bytes
already pulled. This applies equally to success and broken exits. -/
theorem fast_body_stream_budget {start finish : IL} {bs : List UInt8}
    {used consumed : Nat} (usedBound : used ≤ bs.length)
    (trace : stream finish (bs.drop used) = (stream start bs).drop consumed) :
    finish.bits.toNat ≤ start.bits.toNat + 8 * used := by
  have shorter : (stream finish (bs.drop used)).length ≤ (stream start bs).length := by
    rw [trace]
    simp
  simp only [stream, List.length_append, natBits_length, bytesBits_length,
    List.length_drop] at shorter
  omega

/-- The actual fast body retains the public input packet on every branch,
including a broken decode. The output bound is joined from the same run. -/
theorem FastInputPacket.fast_body_view_post
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
      Space.get after dest = some array ∧ array.size = output.size := by
  let bs := first :: second :: third :: fourth :: fifth :: sixth :: rest
  obtain ⟨outputResult, outputAfter, array, next, outputRun, outputOut,
    lower, upper, bytes, size⟩ :=
    packet.fast_body_output_bound invariant buffers streamPtr statePtr mode
      whaveEq wsizeEq wnextEq windowEq lcodePtr codesGet safe lenMask
      dcodePtr distGet distSafe distMask bitsBound left avail outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current beginLe span guard
  by_cases small : slow.bits.toNat < 15
  · obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      usedBound, consumedBound, bodyRun, finalPacket, finalInvariant,
      finalBuffers, sizes, trace⟩ :=
      packet.fast_body_pull_branch_default_state invariant buffers
        streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
        lcodePtr codesGet safe lenMask dcodePtr distGet distSafe distMask
        small left avail outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have same := Except.ok.inj (bodyRun.symm.trans outputRun)
    have resultEq : result = outputResult := (congrArg Prod.fst same)
    have afterEq : after = outputAfter := (congrArg Prod.snd same)
    subst outputResult
    subst outputAfter
    have usedInBs : used ≤ bs.length := by simp [bs]; omega
    have bitBudget := fast_body_stream_budget usedInBs trace
    exact ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      array, next, by omega, consumedBound, bodyRun, finalPacket,
      finalInvariant, finalBuffers, sizes, trace, finalPacket.cursor,
      finalPacket.bits, bitBudget, outputOut, lower, upper, bytes, size⟩
  · have held : 15 ≤ slow.bits.toNat := by omega
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    obtain ⟨root, addRun, selectedPacket⟩ :=
      packet.fast_body_root_lookup lcodePtr codesGet safe lenMask
    obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      usedBound, consumedBound, loopRun, finalPacket, finalInvariant,
      finalBuffers, sizes, trace⟩ :=
      selectedPacket.dolen_root_complete_default_state invariant buffers
        streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
        rfl lcodePtr codesGet safe root dcodePtr distGet distSafe distMask
        held bitsBound left avail outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have noPull : ¬ l.bits < 15 := by
      intro less
      have below : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp less
      omega
    have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after)
      unfold Zlib.Inffast.inflate_fast_body
      simp only [noPull, ite_false]
      change (Ptr.add c.lcode rootSlice >>= fun here =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current))
          { l with here }) h = .ok (result, after)
      change Ptr.add c.lcode rootSlice h =
        .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
      rw [bind_ok addRun]
      exact loopRun
    have same := Except.ok.inj (bodyRun.symm.trans outputRun)
    have resultEq : result = outputResult := congrArg Prod.fst same
    have afterEq : after = outputAfter := congrArg Prod.snd same
    subst outputResult
    subst outputAfter
    have usedInBs : used ≤ bs.length := by simp [bs]; omega
    have bitBudget := fast_body_stream_budget usedInBs trace
    exact ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      array, next, by omega, consumedBound, bodyRun, finalPacket,
      finalInvariant, finalBuffers, sizes, trace, finalPacket.cursor,
      finalPacket.bits, bitBudget, outputOut, lower, upper, bytes, size⟩

#print axioms FastInputPacket.fast_body_view_post
end Zlib.Inflate.Proofs
