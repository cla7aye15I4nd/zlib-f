import ZlibF.Proof.«inflate.c.fast-view-literal-progress-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-classify-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- When the selected second-level length-table cell is a literal, the
actual two-pass loop advances the output pointer exactly once. -/
theorem FastInputPacket.dolen_linked_literal_progress
    {h after : Heap} {slow : IL} {bs : List UInt8}
    {l linked result : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice slice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    (firstRun : C.run (Zlib.Inffast.dolen c l) h =
      .ok (linked, h))
    (linkedHere : linked.here = .ref codeRef
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat +
        slice))
    (sliceBound : slice <
      2 ^ (codes.getD (baseOff + rootSlice) default).op.toNat)
    (literal : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat +
        slice) default).op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (run : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h = .ok (result, after)) :
    result.out = .ref dest (j + 1) := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨actual, actualSlice, actualRun, actualBound,
    actualHere, againL, _, actualOut, _, actualPacket,
    _, actualBuffers, actualSource⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  have linkedHere' : linked.here = .ref codeRef
      (baseOff + codes[baseOff + rootSlice].val.toNat + slice) := by
    simpa only [rootEq] using linkedHere
  have sliceEq : actualSlice = slice := by
    have unique := dolen_link_slice_unique actualRun firstRun
      actualHere linkedHere'
    exact unique.2
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + actualSlice
  have target := len_table_link_source_cases safe root link
    (by simpa only [rootEq, ← sliceEq] using sliceBound)
  have targetBound : targetIndex < codes.size := by
    simpa only [targetIndex, rootEq] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [targetIndex, rootEq, targetEq] using target.2.1
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using actualSource)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have total := targetLeaf.1
    omega
  have targetLiteral : codes[targetIndex].op = 0 := by
    simpa only [targetIndex, rootEq, targetEq, ← sliceEq]
      using literal
  have targetHere : actual.here = .ref codeRef targetIndex := by
    simpa only [targetIndex, rootEq] using actualHere
  have actualOutPtr : actual.out = .ref dest j :=
    actualOut.trans outPtr
  have actualPut : slowLink.put = .ref dest oo := outputPtr
  have actualEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have actualLeft : slowLink.left ≠ 0 := left
  have actualAvail : 258 ≤ slowLink.left.toNat := avail
  have actualSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have actualGuard : C.run (Ptr.lt actual.out c.end_) h =
      .ok (true, h) := by
    simpa only [actualOutPtr, outPtr] using guard
  have actualLoopRun : C.run (cdoWhile
      (Zlib.Inffast.dolen c)
      (fun q => pure (q.againL, q)) l) h =
      .ok (result, after) := run
  exact actualPacket.dolen_linked_literal_output_advance
    invariant actualBuffers actualRun againL targetHere
    codesGet targetBound targetFits targetWidth targetLiteral
    actualLeft actualAvail actualOutPtr actualPut actualEnd
    outputGet outputWrite actualSize current actualGuard
    actualLoopRun

end Zlib.Inflate.Proofs
