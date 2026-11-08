import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dodist-root-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A safe actual root distance entry writes only up to its returned cursor,
including linked and invalid entries that write no output bytes. -/
theorem FastInputPacket.dodist_root_exact_frame
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
    ∃ result after k,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
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
    obtain ⟨result, after, k, run, out, lower, frame⟩ :=
      packet.dodist_base_leaf_exact_frame invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet indexBound bitsFit codeWidth baseBool
        extras left avail length outPtr outputPtr begPtr endPtr
        outputGet outputWrite outputSize current beginLe span guard
    exact ⟨result, after, k, run, out, lower, frame⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, linkClass.1, bne_self_eq_false]
    have linkBool : (entry.op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp only [entry, linkClass.2.1, beq_self_eq_true]
    obtain ⟨result, slice, run, _, _, _, _, out, _, _, _, _, _⟩ :=
      packet.dodist_link_default_state_exact invariant buffers
        herePtr dcodePtr codesGet indexBound bitsFit codeWidth
        notBase linkBool linkClass.2.2.2.1
        linkClass.2.2.2.2
    have frame : BufferFrame h h
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j - oo⟩] := by
      rw [outputPtr]
      exact BufferFrame.singleton_refl outputGet outputWrite
    exact ⟨result, h, j, run, by rw [out]; exact outPtr,
      current, frame⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, invalidClass.1, bne_self_eq_false]
    have notLink : (entry.op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [entry, invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, againD, _, out, _, _, _, _, _⟩ :=
      packet.dodist_invalid_leaf_default_state invariant buffers
        streamPtr statePtr herePtr codesGet indexBound bitsFit
        codeWidth notBase notLink
    have frame : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j - oo⟩] := by
      rw [heapEq]
      exact (badHeap_buffer_frame invariant.good.live.hz
        invariant.good.live.hs i [⟨slow.put, j - oo⟩]).1
    exact ⟨result, after, j, run, by rw [out]; exact outPtr,
      current, frame⟩

#print axioms FastInputPacket.dodist_root_exact_frame

end Zlib.Inflate.Proofs
