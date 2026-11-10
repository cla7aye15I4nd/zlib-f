import ZlibF.Proof.«inflate.c.fast-view-distance-class»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual translated distance pass classifies every safe root table
entry and retains the default state and caller buffer packet on all exits. -/
theorem FastInputPacket.dodist_root_default_state
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
    {baseOff rootBits rootIndex : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootIndex))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
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
    let codeIndex := baseOff + rootIndex
    let entry := codes.getD codeIndex default
    ∃ used slowNext result after,
      used ≤ 2 ∧
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: rest).drop used) result ∧
      DispatchBuffers after r slowNext
        ((first :: second :: rest).drop used) ∧
      ByteViewSizes h after ∧
      ((∃ slice,
        after = h ∧ result.againD = true ∧
        slice < 2 ^ entry.op.toNat ∧
        result.here = .ref codeRef
          (baseOff + entry.val.toNat + slice) ∧
        DistLeaf entry.bits.toNat
          (codes.getD (baseOff + entry.val.toNat + slice)
            default) ∧
        stream slowNext ((first :: second :: rest).drop used) =
          (stream slow (first :: second :: rest)).drop
            entry.bits.toNat) ∨
       (∃ extraUsed, extraUsed ≤ 13 ∧
        FastDistancePost h after r zs z s slowNext
          ((first :: second :: rest).drop used) result
          dest output j l.len.toNat ∧
        stream slowNext ((first :: second :: rest).drop used) =
          ((stream slow (first :: second :: rest)).drop
            entry.bits.toNat).drop extraUsed) ∨
       (∃ i,
        result.broke = true ∧ result.againD = false ∧
        after = badHeap h r zs z s i ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 }
          { s with mode := BAD } ∧
        stream slowNext ((first :: second :: rest).drop used) =
          (stream slow (first :: second :: rest)).drop
            entry.bits.toNat)) := by
  have cases := dist_table_root_cases safe root
  dsimp only at cases ⊢
  obtain ⟨indexBound, codeWidth, classified⟩ := cases
  have entryEq : codes.getD (baseOff + rootIndex) default =
      codes[baseOff + rootIndex] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  rw [entryEq] at codeWidth classified
  let entry : Code := codes[baseOff + rootIndex]
  have bitsFit : entry.bits.toNat ≤ slow.bits.toNat := by
    simpa only [entry] using
      (show codes[baseOff + rootIndex].bits.toNat ≤
        slow.bits.toNat by omega)
  rcases classified with baseClass | linkClass | invalidClass
  · have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simpa only [entry, bne_iff_ne] using baseClass.1
    have extras : (entry.op.toUInt32 &&& 15).toNat ≤ 13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      simpa only [entry] using baseClass.2.1
    obtain ⟨used, slowNext, result, after, bound, run,
      post, source⟩ :=
      packet.dodist_base_leaf_default_state invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet indexBound bitsFit codeWidth baseBool
        extras left avail length outPtr outputPtr begPtr endPtr
        outputGet outputWrite outputSize current beginLe span guard
    exact ⟨used, slowNext, result, after, bound, run,
      post.1, post.2.1, post.2.2.1,
      Or.inr (Or.inl ⟨(entry.op.toUInt32 &&& 15).toNat,
        extras, post, by simpa only [entryEq] using source⟩)⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, linkClass.1, bne_self_eq_false]
    have linkBool : (entry.op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp only [entry, linkClass.2.1, beq_self_eq_true]
    obtain ⟨result, slowNext, slice, run, sliceBound,
      here, againD, _, _, _, packetAfter, _, buffersAfter, source⟩ :=
      packet.dodist_link_default_state invariant buffers
        herePtr dcodePtr codesGet indexBound bitsFit codeWidth
        notBase linkBool linkClass.2.2.2.1
        linkClass.2.2.2.2
    have link : DistLink (codes.getD
        (baseOff + rootIndex) default) := by
      rw [entryEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    have target := dist_table_link_target safe root link
      (by simpa only [entryEq] using sliceBound)
    exact ⟨0, slowNext, result, h, by omega,
      run, by simpa using packetAfter,
      by simpa using buffersAfter,
      ByteViewSizes.refl h,
      Or.inl ⟨slice, rfl, againD,
        by simpa only [entryEq] using sliceBound,
        by simpa only [entryEq] using here,
        by simpa only [entryEq] using target.2.1,
        by simpa [entryEq] using source⟩⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, invalidClass.1, bne_self_eq_false]
    have notLink : (entry.op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [entry, invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, againD, _, _, packetAfter, stateAfter,
      buffersAfter, sizes, source⟩ :=
      packet.dodist_invalid_leaf_default_state invariant buffers
        streamPtr statePtr herePtr codesGet indexBound bitsFit
        codeWidth notBase notLink
    exact ⟨0, slowNext, result, after, by omega,
      run, by simpa using packetAfter,
      by simpa using buffersAfter, sizes,
      Or.inr (Or.inr ⟨i, broke, againD, heapEq,
        stateAfter, by simpa [entryEq] using source⟩)⟩

/-- A linked distance leaf fits the held bits after the root code is
consumed. The bound follows from the unchanged unread byte suffix. -/
theorem linked_distance_leaf_bits_fit
    {slow next : IL} {bs : List UInt8}
    {rootBits leafBits : Nat}
    (held : 15 ≤ slow.bits.toNat)
    (rootFits : rootBits ≤ slow.bits.toNat)
    (total : leafBits + rootBits ≤ 15)
    (source : stream next bs = (stream slow bs).drop rootBits) :
    leafBits ≤ next.bits.toNat := by
  have lengths := congrArg List.length source
  simp only [stream, List.length_append, natBits_length,
    bytesBits_length, List.length_drop] at lengths
  omega

end Zlib.Inflate.Proofs
