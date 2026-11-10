import ZlibF.Proof.«inflate.c.fast-view-break-refill-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The selected root entry is an end-of-block code. This is a proof-side
case predicate on the actual registers after the two source pulls. -/
def FastRootEnd (codes : Array Code) (baseOff : Nat)
    (c : Zlib.Inffast.Ctx) (q : Zlib.Inffast.L) : Prop :=
  let index := baseOff + (q.hold &&& c.lmask.toUInt64).toNat
  let entry := codes.getD index default
  index < codes.size ∧
  entry.bits.toNat ≤ 15 ∧
  entry.op ≠ 0 ∧
  (entry.op.toUInt32 &&& 16 != 0) = false ∧
  (entry.op.toUInt32 &&& 64 == 0) = false ∧
  (entry.op.toUInt32 &&& 32 != 0) = true

/-- When the first fast body refills twice and then sees an end-of-block
root code, its actual execution keeps the call-entry input account. -/
theorem FastInputPacket.fast_body_two_pull_end_account_default_state
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
    (rootEnd : FastRootEnd codes baseOff c
      (fastTwoPulls slow first second l)) :
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
    bitsBound2, stream2⟩ :=
    packet.two_pulls_account_default_state invariant buffers
      account small cursor
  let rootSlice := (fast2.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet2.fast_body_root_lookup lcodePtr codesGet safe lenMask
  have class2 : FastRootEnd codes baseOff c fast2 := by
    rw [fast2Eq]
    exact rootEnd
  rcases class2 with ⟨indexBound, codeWidth, nonzero,
    notBase, notLink, endCode⟩
  have entryEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    rw [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem indexBound]
    rfl
  rw [entryEq] at codeWidth nonzero notBase notLink endCode
  have codeBits : codes[baseOff + rootSlice].bits.toNat ≤
      slow2.bits.toNat := by omega
  have selectedAccount : FastInputAccount ctx startOff
      startBits selected :=
    account2.no_pull rfl (Nat.le_refl _)
  obtain ⟨result, slowNext, loopRun, broke,
    nextAccount, nextPacket, nextState, nextBuffers⟩ :=
    selectedPacket.dolen_root_end_loop_account_default_state
      selectedAccount invariant buffers2 statePtr mode rfl
      codesGet indexBound codeBits codeWidth nonzero
      notBase notLink endCode
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
