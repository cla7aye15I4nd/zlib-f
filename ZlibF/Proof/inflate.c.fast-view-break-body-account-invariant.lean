import ZlibF.Proof.«inflate.c.fast-view-break-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-refill-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast body without an initial refill reaches the root
end-of-block `break` while retaining its call-entry input account. -/
theorem FastInputPacket.fast_body_no_pull_end_account_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (account : FastInputAccount ctx startOff startBits l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (indexBound : baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat < codes.size)
    (codeBits : codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].bits.toNat ≤
        slow.bits.toNat)
    (codeWidth : codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].bits.toNat ≤ 15)
    (nonzero : codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].op ≠ 0)
    (notBase : (codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].op.toUInt32 &&&
      16 != 0) = false)
    (notLink : (codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].op.toUInt32 &&&
      64 == 0) = false)
    (endCode : (codes[baseOff +
      (l.hold &&& c.lmask.toUInt64).toNat].op.toUInt32 &&&
      32 != 0) = true) :
    ∃ result slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, setI h zs { s with mode := TYPE }) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket (setI h zs { s with mode := TYPE })
        slowNext bs result ∧
      DefaultStateJ (setI h zs { s with mode := TYPE })
        r zs z { s with mode := TYPE } ∧
      DispatchBuffers (setI h zs { s with mode := TYPE })
        r slowNext bs := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe lenMask
  have selectedAccount : FastInputAccount ctx startOff
      startBits selected :=
    account.no_pull rfl (Nat.le_refl _)
  obtain ⟨result, slowNext, loopRun, broke,
    nextAccount, nextPacket, nextState, nextBuffers⟩ :=
    selectedPacket.dolen_root_end_loop_account_default_state
      selectedAccount invariant buffers statePtr mode rfl
      codesGet indexBound codeBits codeWidth nonzero
      notBase notLink endCode
  have noPull : ¬ l.bits < 15 := by
    intro less
    have bound := UInt32.lt_iff_toNat_lt.mp less
    rw [packet.bits] at bound
    simp at bound
    omega
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, setI h zs { s with mode := TYPE }) := by
    change (Zlib.Inffast.inflate_fast_body c l) h = _
    unfold Zlib.Inffast.inflate_fast_body
    simp only [noPull, ite_false]
    change (Ptr.add c.lcode rootSlice >>= fun here =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current))
        { l with here }) h = _
    change Ptr.add c.lcode rootSlice h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    change (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current))
      selected) h =
        .ok (result, setI h zs { s with mode := TYPE }) at loopRun
    simp only [bind_app, addRun, loopRun, rootSlice,
      selected]
  exact ⟨result, slowNext, bodyRun, broke,
    nextAccount, nextPacket, nextState, nextBuffers⟩

end Zlib.Inflate.Proofs
