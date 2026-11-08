import ZlibF.Proof.«inflate.c.fast-view-body-no-pull-branch-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-root-complete-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The no-refill actual fast body retains the complete root decoder's
output, BAD or TYPE heap effect. -/
theorem FastInputPacket.fast_body_no_pull_output_effect
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
    (held : 15 ≤ slow.bits.toNat)
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
    ∃ slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      FastOutputEffect h after r zs z s slowFinal dest ∧
      (result.broke = false →
        slowFinal.put = slow.put ∧ slowFinal.left = slow.left) := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe lenMask
  obtain ⟨slowFinal, result, after, loopRun, effect, frame⟩ :=
    selectedPacket.dolen_root_complete_output_effect
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq rfl lcodePtr codesGet
      safe root dcodePtr distGet distSafe distMask held
      bitsBound left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have noPull : ¬ l.bits < 15 := by
    intro less
    have below : slow.bits.toNat < 15 := by
      rw [← packet.bits]
      simpa using UInt32.lt_iff_toNat_lt.mp less
    omega
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after)
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
  exact ⟨slowFinal, result, after, bodyRun, effect, frame⟩

#print axioms FastInputPacket.fast_body_no_pull_output_effect

end Zlib.Inflate.Proofs
