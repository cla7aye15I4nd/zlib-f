import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-end-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- If the selected second-level length leaf is invalid, the actual
two-pass `dolen` loop enters BAD and retains the default relation. -/
theorem FastInputPacket.dolen_linked_invalid_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
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
        (target.op.toUInt32 &&& 32 != 0) = false) →
        ∃ i result slowFinal after,
          C.run (Zlib.Inffast.dolen c linked) h =
            .ok (result, after) ∧
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          after = badHeap h r zs z s i ∧
          result.broke = true ∧ result.againL = false ∧
          FastInputPacket after slowFinal bs result ∧
          DefaultStateJ after r zs
            { z with msg := .ref (.str i) 0 }
            { s with mode := BAD } ∧
          DispatchBuffers after r slowFinal bs ∧
          ByteViewSizes h after ∧
          stream slowFinal bs = (stream slow bs).drop
            (rootEntry.bits.toNat +
              (codes.getD (baseOff + rootEntry.val.toNat + slice)
                default).bits.toNat)) := by
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetBits,
    linkedPacket, _, linkedBuffers, linkedSource⟩ :=
    packet.dolen_root_link_default_state invariant buffers
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
  have invalid : codes[targetIndex].op ≠ 0 ∧
      (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 32 != 0) = false := by
    simpa only [targetIndex, targetEq] using selected
  obtain ⟨i, after, result, slowFinal, secondRun,
    heapEq, broke, noAgain, _, _, finalPacket,
    finalState, finalBuffers, sizes, source⟩ :=
    linkedPacket.dolen_invalid_leaf_default_state
      invariant linkedBuffers streamPtr statePtr
      targetHere codesGet targetBound targetFits targetWidth
      invalid.1 invalid.2.1 invalid.2.2.1
      invalid.2.2.2
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  refine ⟨i, result, slowFinal, after, secondRun,
    loopRun, heapEq, broke, noAgain, finalPacket,
    finalState, finalBuffers, sizes, ?_⟩
  rw [linkedSource] at source
  simpa only [targetIndex, targetEqNorm,
    Nat.add_assoc, List.drop_drop] using source

end Zlib.Inflate.Proofs
