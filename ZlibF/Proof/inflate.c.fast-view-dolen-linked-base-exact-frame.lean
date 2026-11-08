import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-base-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked base-length leaf changes only the final output prefix. -/
theorem FastInputPacket.dolen_linked_base_exact_frame
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
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
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op &&& 16 ≠ 0 ∧
        (target.op &&& 15).toNat ≤ 5 ∧
        3 ≤ target.val.toNat ∧
        target.val.toNat +
          2 ^ (target.op &&& 15).toNat ≤ 259) →
        ∃ result after k,
          C.run (Zlib.Inffast.dolen c linked) h =
            .ok (result, after) ∧
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest k ∧
          oo ≤ k ∧
          BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
            [⟨slow.put, k - oo⟩]) := by
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
  have linkedOut : linked.out = .ref dest j :=
    linkedOutEq.trans outPtr
  let rootCount : UInt32 :=
    codes[baseOff + rootSlice].bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := rootCount }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have rootCountFits : rootCount.toNat ≤ slow.bits.toNat := by
    simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
      using rootFits
  have rootCountSmall : rootCount.toNat < 64 := by
    have width : rootCount.toNat ≤ 15 := by
      simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
        using rootWidthBound
    omega
  have dropped := firstPacket.drop_bits_default_state
    buffers rootCount rootCountFits rootCountSmall
  have linkedBitsBound : slowLink.bits.toNat ≤ 30 := by
    have remaining : slowLink.bits.toNat =
        slow.bits.toNat - rootCount.toNat := by
      simpa only [slowLink, rootCount] using dropped.2.2.2
    omega
  have linkedPut : slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut, outPtr] using guard
  refine ⟨linked, slice, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using linkedHere,
    ?_⟩
  intro selectedBase
  have base : codes[targetIndex].op &&& 16 ≠ 0 ∧
      (codes[targetIndex].op &&& 15).toNat ≤ 5 ∧
      3 ≤ codes[targetIndex].val.toNat ∧
      codes[targetIndex].val.toNat +
        2 ^ (codes[targetIndex].op &&& 15).toNat ≤ 259 := by
    simpa only [rootEq, targetIndex, targetEq] using selectedBase
  obtain ⟨result, after, k, secondRun, out, lower, frame⟩ :=
    linkedPacket.dolen_base_leaf_exact_frame invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  obtain ⟨_, _, _, _, oldResult, oldAfter, _, _, _,
      oldRun, noAgain, _, _, _, _, _, _, _⟩ :=
    linkedPacket.dolen_base_leaf_frame_default_state invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  have same : oldResult = result ∧ oldAfter = after := by
    rw [secondRun] at oldRun
    cases oldRun
    exact ⟨rfl, rfl⟩
  have noAgainExact : result.againL = false := by
    rw [← same.1]
    exact noAgain
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgainExact, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  exact ⟨result, after, k, secondRun, loopRun, out, lower,
    by simpa only [slowLink] using frame⟩

#print axioms FastInputPacket.dolen_linked_base_exact_frame

end Zlib.Inflate.Proofs
