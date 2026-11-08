import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-invariant»
import ZlibF.Proof.«inffast.c.dist-selected-ledger»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual root-link and leaf distance calls charge all reads to one cursor count, including invalid and bad-distance exits. -/
theorem FastInputPacket.dodist_linked_leaf_bit_budget
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
    ∃ linked result after pulled,
      pulled ≤ 2 ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) ∧
      linked.againD = true ∧ result.againD = false ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨linked, slice, firstRun, againD, sliceBound,
      here, leaf, usedGhost, slowNext, result, after,
      usedBound, secondRun, finalPacket, finalBuffers,
      sizes, outcome⟩ :=
    packet.dodist_linked_leaf_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr dcodePtr codesGet safe root link held left avail
      length outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  let rootEntry := codes[baseOff + rootSlice]
  have rootLink : DistLink rootEntry := by
    simpa only [rootEntry, rootEq] using link
  have rootWidthBound : rootEntry.bits.toNat ≤ 15 := by
    have chosen := safe.2.2 rootSlice root
    rw [rootEq, if_pos rootLink] at chosen
    exact chosen.1
  have rootHeld : rootEntry.bits.toNat ≤ l.bits.toNat := by
    rw [packet.bits]
    omega
  have rootNonbase : (rootEntry.op.toUInt32 &&& 16 != 0) = false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.1]
  have rootLoad : Ptr.load l.here h = .ok (rootEntry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet rootBound
  obtain ⟨rootCursor, rootBits⟩ :=
    Zlib.Inffast.Proofs.dodist_nonbase_bit_ledger
      rootLoad rootHeld rootWidthBound rootNonbase
      (by simpa only [C.run] using firstRun)
  let targetIndex := baseOff + rootEntry.val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    have target := dist_table_link_target safe root link
      (by simpa only [rootEq] using sliceBound)
    simpa only [rootEq, rootEntry, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetLeaf : DistLeaf rootEntry.bits.toNat codes[targetIndex] := by
    simpa only [rootEq, rootEntry, targetIndex, targetEq] using leaf
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [rootEq, rootEntry, targetIndex] using here
  have targetLoad : Ptr.load linked.here h =
      .ok (codes[targetIndex], h) := by
    rw [targetHere]
    exact Ptr.load_ok codesGet targetBound
  have targetHeld : codes[targetIndex].bits.toNat ≤ linked.bits.toNat := by
    have rootTotal : rootEntry.bits.toNat + codes[targetIndex].bits.toNat ≤ 15 :=
      by simpa only [Nat.add_comm] using targetLeaf.1
    rw [← packet.bits] at held
    omega
  obtain ⟨pulled, pulledBound, leafCursor, leafBudget⟩ :=
    Zlib.Inffast.Proofs.dodist_leaf_bit_budget
      targetLoad targetHeld targetLeaf
      (by simpa only [C.run] using secondRun)
  have noAgain : result.againD = false := by
    rcases targetLeaf.2 with base | invalid
    · have baseBool : (codes[targetIndex].op.toUInt32 &&& 16 != 0) = true := by
        rw [Zlib.Inffast.Proofs.mask16]
        simp [base.1]
      exact Zlib.Inffast.Proofs.dodist_base_againD_false
        targetLoad (by omega) baseBool (by simpa only [C.run] using secondRun)
    · have nonbase : (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false := by
        rw [Zlib.Inffast.Proofs.mask16]
        simp [invalid.1]
      have notLink : (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false := by
        rw [Zlib.Inffast.Proofs.mask64]
        simp [invalid.2]
      exact Zlib.Inffast.Proofs.dodist_invalid_againD_false
        targetLoad (by omega) nonbase notLink
        (by simpa only [C.run] using secondRun)
  refine ⟨linked, result, after, pulled, pulledBound,
    firstRun, secondRun, againD, noAgain, ?_, ?_⟩
  · rw [leafCursor, rootCursor]
  · omega

#print axioms FastInputPacket.dodist_linked_leaf_bit_budget
end Zlib.Inflate.Proofs
