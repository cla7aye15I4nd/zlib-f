import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-end-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-link-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-end-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- If the selected second-level length leaf ends a block, the actual
two-pass `dolen` loop enters TYPE and retains the default state. -/
theorem FastInputPacket.dolen_linked_end_local_state
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
          C.run (Zlib.Inffast.dolen c linked) h =
            .ok (result, setI h zs { s with mode := TYPE }) ∧
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, setI h zs { s with mode := TYPE }) ∧
          result.broke = true ∧ result.againL = false ∧
          FastInputPacket (setI h zs { s with mode := TYPE })
            slowFinal bs result ∧
          LocalStateJ (setI h zs { s with mode := TYPE })
            cutoff r zs z { s with mode := TYPE } ∧
          DispatchBuffers (setI h zs { s with mode := TYPE })
            r slowFinal bs ∧
          ByteViewSizes h (setI h zs { s with mode := TYPE }) ∧
          stream slowFinal bs = (stream slow bs).drop
            (rootEntry.bits.toNat +
              (codes.getD (baseOff + rootEntry.val.toNat + slice)
                default).bits.toNat)) := by
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetBits,
    linkedPacket, _, linkedBuffers, linkedSource⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dolen_root_link_local_state packet) invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have target := len_table_link_target safe root link sliceBound
  let targetIndex : Nat := baseOff +
    (codes.getD (baseOff + rootSlice) default).val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)) default =
      codes[baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
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
    _, _, finalPacket, finalState, finalBuffers,
    sizes, source⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dolen_end_leaf_local_state linkedPacket) invariant
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
  refine ⟨result, slowFinal, secondRun, loopRun,
    broke, noAgain, finalPacket, finalState, finalBuffers,
    sizes, ?_⟩
  rw [linkedSource] at source
  simpa only [targetIndex, targetEqNorm,
    Nat.add_assoc, List.drop_drop]
    using source

end Zlib.Inflate.Local
