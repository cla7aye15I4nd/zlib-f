import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-literal-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- If a selected second-level length leaf is a literal, the actual
two-pass `dolen` loop writes it on the caller output view. -/
theorem FastInputPacket.dolen_linked_literal_output_register_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice slowLink,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      FastInputPacket h slowLink bs linked ∧
      DispatchBuffers h r slowLink bs ∧
      stream slowLink bs = (stream slow bs).drop
        rootEntry.bits.toNat ∧
      ((codes.getD (baseOff + rootEntry.val.toNat + slice)
        default).op = 0 →
        ∃ result slowFinal after,
          C.run (Zlib.Inffast.dolen c linked) h =
            .ok (result, after) ∧
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.againL = false ∧
          FastInputPacket after slowFinal bs result ∧
          DefaultStateJ after r zs z s ∧
          DispatchBuffers after r slowFinal bs ∧
          ByteViewSizes h after ∧
          Space.get after dest = some
            (output.set! j
              (codes.getD (baseOff + rootEntry.val.toNat + slice)
                default).val.toUInt8) ∧
          Space.ro after dest = false ∧
          BufferFrame h after (fun _ => False)
            [⟨slow.put, slow.left.toNat⟩] ∧
          stream slowFinal bs =
            (stream slow bs).drop
              (rootEntry.bits.toNat +
                (codes.getD
                  (baseOff + rootEntry.val.toNat + slice)
                  default).bits.toNat) ∧
          slowFinal.put = slow.put ∧
          slowFinal.left = slow.left ∧
          slowFinal.out_ = slow.out_ ∧
          slowFinal.next = slow.next ∧
          slowFinal.have_ = slow.have_ ∧
          result.in_ = l.in_) := by
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
  obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
    againL, _, linkedOutEq, _, linkedPacket, _,
    linkedBuffers, linkedSource⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have linkedOut : linked.out = .ref dest j :=
    linkedOutEq.trans outPtr
  have target := len_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq]
      using target.2.1
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using linkedSource)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width := targetLeaf.1
    omega
  have linkedPut : slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut, outPtr] using guard
  refine ⟨linked, slice, slowLink, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using linkedHere,
    linkedPacket, linkedBuffers,
    by simpa only [rootEq] using linkedSource, ?_⟩
  intro literal
  have targetLiteral : codes[targetIndex].op = 0 := by
    simpa only [rootEq, targetIndex, targetEq]
      using literal
  let count : UInt32 := codes[targetIndex].bits.toUInt32
  let slowFinal : IL := { slowLink with
    hold := slowLink.hold >>> count.toUInt64,
    bits := slowLink.bits - count }
  let result : Zlib.Inffast.L := { linked with
    againL := false,
    op := codes[targetIndex].op.toUInt32,
    hold := linked.hold >>> count.toUInt64,
    bits := linked.bits - count,
    out := .ref dest (j + 1) }
  let after := Space.put h dest
    (output.set! j codes[targetIndex].val.toUInt8)
  have second := linkedPacket.dolen_literal_default_state
    invariant linkedBuffers targetHere codesGet targetBound
    targetFits targetWidth targetLiteral
    (by simpa only [slowLink] using left)
    (by simpa only [slowLink] using avail)
    linkedOut linkedPut linkedEnd outputGet outputWrite
    linkedSize current linkedGuard
  have secondRun : C.run (Zlib.Inffast.dolen c linked) h =
      .ok (result, after) := by
    simpa only [result, after, slowFinal, count]
      using second.1
  have secondAgain : result.againL = false := by
    simpa only [result] using second.2.1
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [secondAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  refine ⟨result, slowFinal, after, secondRun, loopRun,
    secondAgain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [result, slowFinal, after, count]
      using second.2.2.1
  · exact second.2.2.2.1
  · simpa only [result, slowFinal, after, count]
      using second.2.2.2.2.1
  · exact second.2.2.2.2.2.1
  · simpa only [rootEq, targetIndex, targetEqNorm,
      Nat.add_assoc, after]
      using second.2.2.2.2.2.2.2.1
  · exact second.2.2.2.2.2.2.2.2.1
  · exact second.2.2.2.2.2.2.2.2.2
  · have source := second.2.2.2.2.2.2.1
    rw [linkedSource] at source
    simpa only [rootEq, targetIndex, targetEqNorm,
      slowFinal, slowLink, count, Nat.add_assoc,
      List.drop_drop]
      using source
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have linkedInput : linked.in_ = l.in_ := by
      calc
        linked.in_ = slowLink.next := linkedPacket.cursor
        _ = slow.next := rfl
        _ = l.in_ := packet.cursor.symm
    simpa only [result] using linkedInput

end Zlib.Inflate.Proofs
