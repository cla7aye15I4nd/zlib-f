import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked distance entry retains the fast held-bit bound on every
nonbreaking exit from its second-level leaf. -/
theorem FastInputPacket.dodist_linked_leaf_bits_default_state
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : DistLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
    ∃ linked used slowNext result after,
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dodist c linked) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: rest).drop used) result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨linked, slice, firstRun, _, sliceBound, here,
    leaf, used, slowNext, result, after, _, secondRun,
    finalPacket, _, _, _, _⟩ :=
    packet.dodist_linked_leaf_frame_default_state invariant
      buffers streamPtr statePtr whaveEq wsizeEq wnextEq
      windowEq herePtr dcodePtr codesGet safe root link
      held left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : DistLink codes[baseOff + rootSlice] := by
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
    simp [rootLink.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked0, _, firstRun0, _, _, _, _, linkedOut0,
    linkedLen0, linkedPacket0, _, linkedBuffers0, source0⟩ :=
    packet.dodist_link_default_state_exact invariant buffers
      herePtr dcodePtr codesGet rootBound rootFits
      rootWidthBound notBase linkBool opWidth subtable
  rw [firstRun] at firstRun0
  cases firstRun0
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have linkBound : slowLink.bits.toNat ≤ 30 := by
    change (slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32).toNat ≤ 30
    have countLe :
        codes[baseOff + rootSlice].bits.toUInt32.toNat ≤
          slow.bits.toNat := by
      simpa only [Zlib.Inffast.Proofs.toNat32] using rootFits
    rw [UInt32.toNat_sub_of_le _ _
      (UInt32.le_iff_toNat_le.mpr countLe)]
    omega
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    have target := dist_table_link_target safe root link
      (by simpa only [rootEq] using sliceBound)
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetLeaf : DistLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq] using leaf
  have targetBits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using source0)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    omega
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [rootEq, targetIndex] using here
  have targetOut : linked.out = .ref dest j := by
    exact linkedOut0.trans outPtr
  have targetLength : 3 ≤ linked.len.toNat ∧
      linked.len.toNat ≤ 258 := by
    simpa only [linkedLen0] using length
  have targetGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    rw [targetOut]
    simpa only [outPtr] using guard
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    rcases targetLeaf.2 with baseClass | invalidClass
    · have baseBool :
          (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
            true := by
        rw [Zlib.Inffast.Proofs.mask16]
        simp [baseClass.1]
      have extraBound :
          (codes[targetIndex].op.toUInt32 &&& 15).toNat ≤
            13 := by
        rw [Zlib.Inffast.Proofs.mask15]
        exact baseClass.2.1
      obtain ⟨_, slowBase, result0, after0, _, run0,
        post0, _, _, _, _, _, bound0⟩ :=
        linkedPacket0.dodist_base_leaf_bits_default_state
          invariant linkedBuffers0 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq targetHere
          codesGet targetBound targetBits targetWidth
          baseBool extraBound linkBound left avail
          targetLength targetOut outputPtr begPtr endPtr
          outputGet outputWrite outputSize current beginLe
          span targetGuard
      rw [secondRun] at run0
      cases run0
      have sameBits : slowNext.bits = slowBase.bits :=
        finalPacket.bits.symm.trans post0.1.bits
      rw [sameBits]
      exact bound0
    · have notBaseLeaf :
          (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
            false := by
        rw [Zlib.Inffast.Proofs.mask16]
        simp [invalidClass.1]
      have notLinkLeaf :
          (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
            false := by
        rw [Zlib.Inffast.Proofs.mask64]
        simp [invalidClass.2]
      obtain ⟨_, after0, result0, _, run0, _,
        broke0, _, _, _, _, _, _, _, _⟩ :=
        linkedPacket0.dodist_invalid_leaf_default_state
          invariant linkedBuffers0 streamPtr statePtr
          targetHere codesGet targetBound targetBits
          targetWidth notBaseLeaf notLinkLeaf
      rw [secondRun] at run0
      cases run0
      rw [broke0] at notBroken
      cases notBroken
  exact ⟨linked, used, slowNext, result, after,
    firstRun, secondRun, finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
