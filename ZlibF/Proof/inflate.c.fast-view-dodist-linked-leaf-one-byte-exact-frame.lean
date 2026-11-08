import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-one-byte-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-one-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The linked one-byte distance leaf changes only the output prefix. -/
theorem FastInputPacket.dodist_linked_leaf_one_byte_exact_frame
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
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
    (held : 20 ≤ slow.bits.toNat)
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
    ∃ linked result after k,
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
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
  obtain ⟨linked, slice, firstRun, sliceBound, here,
    againD, _, linkedOut, linkedLen, linkedPacket, _,
    linkedBuffers, source⟩ :=
    packet.dodist_link_default_state_exact invariant buffers
      herePtr dcodePtr codesGet rootBound rootFits
      rootWidthBound notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := dist_table_link_target safe root link
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
  have targetLeaf : DistLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq] using target.2.1
  have targetBits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit (by omega) rootFits targetLeaf.1
      (by simpa only [slowLink] using source)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    omega
  have targetHeld : 5 + codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    have rootWidthNat :
        codes[baseOff + rootSlice].bits.toUInt32.toNat =
          codes[baseOff + rootSlice].bits.toNat := by
      rfl
    have slowLinkBits : slowLink.bits.toNat =
        slow.bits.toNat - codes[baseOff + rootSlice].bits.toNat := by
      simp only [slowLink]
      rw [UInt32.toNat_sub_of_le _ _
        (UInt32.le_iff_toNat_le.mpr (by
          rw [rootWidthNat]
          exact rootFits))]
      rw [rootWidthNat]
    have total := targetLeaf.1
    omega
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using here
  have targetOut : linked.out = .ref dest j := linkedOut.trans outPtr
  have targetLen : 3 ≤ linked.len.toNat ∧
      linked.len.toNat ≤ 258 := by
    simpa only [linkedLen] using length
  have targetGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut] using guard
  rcases targetLeaf.2 with baseClass | invalidClass
  · have baseBool :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) = true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extraBound :
        (codes[targetIndex].op.toUInt32 &&& 15).toNat ≤ 13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, k, secondRun, out, lower, frame⟩ :=
      linkedPacket.dodist_base_leaf_one_byte_exact_frame invariant
        linkedBuffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq targetHere codesGet targetBound
        targetBits targetWidth targetHeld baseBool extraBound
        (by simpa only [slowLink] using left)
        (by simpa only [slowLink] using avail)
        targetLen targetOut
        (by simpa only [slowLink] using outputPtr)
        begPtr (by simpa only [slowLink] using endPtr)
        outputGet outputWrite
        (by simpa only [slowLink] using outputSize)
        current beginLe span targetGuard
    exact ⟨linked, result, after, k, firstRun, secondRun,
      out, lower, by simpa only [slowLink] using frame⟩
  · have notBaseLeaf :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLinkLeaf :
        (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, secondRun, heapEq,
      broke, noAgain, _, finalOut, _, _, _, _, _⟩ :=
      linkedPacket.dodist_invalid_leaf_default_state
        invariant linkedBuffers streamPtr statePtr targetHere
        codesGet targetBound targetBits targetWidth
        notBaseLeaf notLinkLeaf
    have frame : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j - oo⟩] := by
      rw [heapEq]
      exact (badHeap_buffer_frame invariant.good.live.hz
        invariant.good.live.hs i [⟨slow.put, j - oo⟩]).1
    exact ⟨linked, result, after, j, firstRun, secondRun,
      by rw [finalOut, linkedOut]; exact outPtr,
      current, frame⟩

#print axioms FastInputPacket.dodist_linked_leaf_one_byte_exact_frame

end Zlib.Inflate.Proofs
