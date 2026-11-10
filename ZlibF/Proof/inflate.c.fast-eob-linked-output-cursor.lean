import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Re-expose the exact cursor already constructed by the actual linked
EOB source proof. This is a proof-only strengthening of its projection. -/
theorem FastInputPacket.dolen_linked_end_output_cursor
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
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
    (held : 15 ≤ slow.bits.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat) :
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
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size ∧ next = j) := by
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
  have terminal : codes[targetIndex].op ≠ 0 ∧
      (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [targetIndex, targetEq] using selected
  obtain ⟨result, slowFinal, secondRun, broke, noAgain,
    _, resultOut, finalPacket, finalState, finalBuffers,
    sizes, source⟩ :=
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
  have linkedOut :=
    packet.dolen_root_link_registers invariant buffers
      herePtr lcodePtr codesGet safe root link held firstRun
  have finalOut : result.out = .ref dest j :=
    resultOut.trans (linkedOut.1.trans outPtr)
  have afterGet : Space.get (setI h zs { s with mode := TYPE })
      dest = some output := by
    rw [byte_view_get_setI]
    exact outputGet
  exact ⟨result, setI h zs { s with mode := TYPE },
    output, j, loopRun, finalOut, Nat.le_refl _,
    cursorBound, afterGet, rfl, rfl⟩

#print axioms FastInputPacket.dolen_linked_end_output_cursor
end Zlib.Inflate.Proofs
