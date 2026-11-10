import ZlibF.Proof.«inflate.c.fast-view-break-linked-root-complete-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-end-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked length root followed by an end-of-block leaf exits the
actual two-pass `dolen` loop with the call-entry input account. -/
theorem FastInputPacket.dolen_linked_end_account_default_state
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
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
        ∃ result slowFinal,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, setI h zs { s with mode := TYPE }) ∧
          result.broke = true ∧ result.againL = false ∧
          FastInputAccount ctx startOff startBits result ∧
          FastInputPacket (setI h zs { s with mode := TYPE })
            slowFinal bs result ∧
          DefaultStateJ (setI h zs { s with mode := TYPE })
            r zs z { s with mode := TYPE } ∧
          DispatchBuffers (setI h zs { s with mode := TYPE })
            r slowFinal bs) := by
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetBits,
    linkedAccount, linkedPacket, _, linkedBuffers, _⟩ :=
    packet.dolen_root_link_complete_account_default_state
      account invariant buffers herePtr lcodePtr codesGet
      safe root link held
  have target := len_table_link_target safe root link sliceBound
  let targetIndex : Nat := baseOff +
    (codes.getD (baseOff + rootSlice) default).val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    rw [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem targetBound]
    rfl
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    simpa only [targetIndex, targetEq] using targetBits
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width :
        (codes.getD targetIndex default).bits.toNat +
          (codes.getD (baseOff + rootSlice) default).bits.toNat ≤
          15 := targetLeaf.1
    rw [targetEq] at width
    omega
  refine ⟨linked, slice, firstRun, againL,
    sliceBound, linkedHere, ?_⟩
  intro selected
  have terminal : codes[targetIndex].op ≠ 0 ∧
      (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [targetIndex, targetEq] using selected
  obtain ⟨result, slowFinal, secondRun, broke, noAgain,
    cursor, _, finalPacket, finalState, finalBuffers,
    _, source⟩ :=
    linkedPacket.dolen_end_leaf_default_state invariant
      linkedBuffers statePtr mode targetHere codesGet
      targetBound targetFits targetWidth terminal.1
      terminal.2.1 terminal.2.2.1 terminal.2.2.2
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, setI h zs { s with mode := TYPE }) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result))
          (setI h zs { s with mode := TYPE }) =
          .ok ((false, result),
            setI h zs { s with mode := TYPE }))
  exact ⟨result, slowFinal, loopRun, broke, noAgain,
    linkedAccount.no_pull_from_stream linkedPacket
      finalPacket cursor source,
    finalPacket, finalState, finalBuffers⟩

end Zlib.Inflate.Proofs
