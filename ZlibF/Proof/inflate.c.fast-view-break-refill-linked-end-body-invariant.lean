import ZlibF.Proof.«inflate.c.fast-view-break-linked-end-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- This proof-side case identifies a linked root whose actually selected
second-level length leaf ends the block. -/
def FastLinkedEnd (h : Heap) (codes : Array Code)
    (baseOff : Nat) (c : Zlib.Inffast.Ctx)
    (q : Zlib.Inffast.L) (codeRef : CodeRef) : Prop :=
  let rootSlice := (q.hold &&& c.lmask.toUInt64).toNat
  let rootEntry := codes.getD (baseOff + rootSlice) default
  let selected : Zlib.Inffast.L :=
    { q with here := .ref codeRef (baseOff + rootSlice) }
  LenLink rootEntry ∧
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c selected) h =
        .ok (linked, h) ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      (let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
       target.op ≠ 0 ∧
       (target.op.toUInt32 &&& 16 != 0) = false ∧
       (target.op.toUInt32 &&& 64 == 0) = false ∧
       (target.op.toUInt32 &&& 32 != 0) = true)

/-- The actual fast body with two input pulls and a linked block-end leaf
keeps the call-entry account through the inner two-pass loop. -/
theorem FastInputPacket.fast_body_two_pull_linked_end_account_default_state
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ctx : FastLoopContext} {startOff startBits off : Nat}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (account : FastInputAccount ctx startOff startBits l)
    (cursor : l.in_ = .ref ctx.inputRef off)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (small : slow.bits.toNat < 15)
    (linkedEnd : FastLinkedEnd h codes baseOff c
      (fastTwoPulls slow first second l) codeRef) :
    ∃ result slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, setI h zs { s with mode := TYPE }) ∧
      result.broke = true ∧
      FastInputAccount ctx startOff startBits result ∧
      FastInputPacket (setI h zs { s with mode := TYPE })
        slowNext (third :: fourth :: fifth :: sixth :: rest)
        result ∧
      DefaultStateJ (setI h zs { s with mode := TYPE })
        r zs z { s with mode := TYPE } ∧
      DispatchBuffers (setI h zs { s with mode := TYPE })
        r slowNext (third :: fourth :: fifth :: sixth :: rest) := by
  obtain ⟨fast1, fast2, slow2, pull1, pull2,
    fast2Eq, packet2, buffers2, account2, held2,
    _, _⟩ :=
    packet.two_pulls_account_default_state invariant buffers
      account small cursor
  let rootSlice := (fast2.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet2.fast_body_root_lookup lcodePtr codesGet safe lenMask
  have class2 : FastLinkedEnd h codes baseOff c fast2 codeRef := by
    rw [fast2Eq]
    exact linkedEnd
  rcases class2 with ⟨link, linkedWitness, sliceWitness,
    firstWitness, hereWitness, terminalWitness⟩
  have selectedAccount : FastInputAccount ctx startOff
      startBits selected :=
    account2.no_pull rfl (Nat.le_refl _)
  obtain ⟨linked, slice, firstRun, _, _, linkedHere,
    finish⟩ :=
    selectedPacket.dolen_linked_end_account_default_state
      selectedAccount invariant buffers2 statePtr mode rfl
      lcodePtr codesGet safe root link (by omega)
  have same := dolen_link_slice_unique firstRun firstWitness
    linkedHere hereWitness
  rcases same with ⟨rfl, rfl⟩
  obtain ⟨result, slowNext, loopRun, broke, _,
    nextAccount, nextPacket, nextState, nextBuffers⟩ :=
    finish terminalWitness
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, setI h zs { s with mode := TYPE }) := by
    change (Zlib.Inffast.inflate_fast_body c l) h = _
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    change (Zlib.Inffast.pull l >>= fun q =>
      Zlib.Inffast.pull q >>= fun q' =>
        Ptr.add c.lcode
          (q'.hold &&& c.lmask.toUInt64).toNat >>= fun here =>
          cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current))
            { q' with here }) h = _
    change Zlib.Inffast.pull l h = .ok (fast1, h) at pull1
    change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at pull2
    change Ptr.add c.lcode rootSlice h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    change (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current))
      selected) h =
        .ok (result, setI h zs { s with mode := TYPE }) at loopRun
    simp only [bind_app, pull1, pull2, addRun, loopRun,
      rootSlice, selected]
  exact ⟨result, slowNext, bodyRun, broke,
    nextAccount, nextPacket, nextState, nextBuffers⟩

end Zlib.Inflate.Proofs
