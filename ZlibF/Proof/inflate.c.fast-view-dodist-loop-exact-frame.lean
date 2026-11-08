import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The complete actual distance loop writes only through its final cursor. -/
theorem FastInputPacket.dodist_loop_exact_frame
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
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h =
          .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  have rootCases := dist_table_root_cases safe root
  dsimp only at rootCases
  obtain ⟨rootBound, rootWidthBound, classes⟩ := rootCases
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  rw [rootEq] at rootWidthBound classes
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have rootLoad : Ptr.load l.here h =
      .ok (codes[baseOff + rootSlice], h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet rootBound
  rcases classes with baseClass | linkClass | invalidClass
  · have baseBool :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) = true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extras :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 15).toNat ≤ 13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, k, run, out, lower, frame⟩ :=
      packet.dodist_base_leaf_exact_frame invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound
        baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    have noAgain := Zlib.Inffast.Proofs.dodist_base_againD_false
      rootLoad rootWidthBound baseBool run
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    exact ⟨result, after, k, loop, out, lower, frame⟩
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, slice, firstRun, againD,
      sliceBound, here, leaf, used, slowNext,
      result, after, usedBound, secondRun,
      finalPacket, finalBuffers, sizes, outcome,
      frameAfter⟩ :=
      packet.dodist_linked_leaf_frame_default_state invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    obtain ⟨linkedExact, resultExact, afterExact, k,
      firstRunExact, secondRunExact, outExact, lower, exactFrame⟩ :=
      packet.dodist_linked_leaf_exact_frame invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    have linkedEq : linkedExact = linked := by
      rw [firstRun] at firstRunExact
      cases firstRunExact
      rfl
    subst linkedExact
    have resultEq : resultExact = result ∧ afterExact = after := by
      rw [secondRun] at secondRunExact
      cases secondRunExact
      exact ⟨rfl, rfl⟩
    rcases resultEq with ⟨rfl, rfl⟩
    let targetIndex : Nat := baseOff +
      codes[baseOff + rootSlice].val.toNat + slice
    have targetBound : targetIndex < codes.size := by
      have bound := linkClass.2.2.2.2
      have sliceLimit : slice <
          2 ^ codes[baseOff + rootSlice].op.toNat := by
        simpa only [rootEq] using sliceBound
      omega
    have targetEq : codes.getD targetIndex default =
        codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetLeaf : DistLeaf
        codes[baseOff + rootSlice].bits.toNat
        codes[targetIndex] := by
      simpa only [rootEq, targetIndex, targetEq] using leaf
    have targetHere : linked.here = .ref codeRef targetIndex := by
      simpa only [rootEq, targetIndex] using here
    have targetLoad : Ptr.load linked.here h =
        .ok (codes[targetIndex], h) := by
      rw [targetHere]
      exact Ptr.load_ok codesGet targetBound
    have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
      omega
    have noAgain : resultExact.againD = false := by
      rcases targetLeaf.2 with base | invalid
      · have baseBool :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) = true := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [base.1]
        exact Zlib.Inffast.Proofs.dodist_base_againD_false
          targetLoad targetWidth baseBool secondRun
      · have notBase :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [invalid.1]
        have notLink :
            (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false := by
          rw [Zlib.Inffast.Proofs.mask64]
          simp [invalid.2]
        exact Zlib.Inffast.Proofs.dodist_invalid_againD_false
          targetLoad targetWidth notBase notLink secondRun
    have condFirst :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          linked h = .ok ((true, linked), h) := by
      simp [againD]
    have condSecond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          resultExact afterExact =
            .ok ((false, resultExact), afterExact) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L)))
      firstRun condFirst secondRun condSecond
    exact ⟨resultExact, afterExact, k, loop, outExact, lower,
      exactFrame⟩
  · have notBase :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLink :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, noAgain, _, out, _, _, _, _, _⟩ :=
      packet.dodist_invalid_leaf_default_state invariant
        buffers streamPtr statePtr herePtr codesGet
        rootBound rootFits rootWidthBound notBase notLink
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    have frame : BufferFrame h after
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, j - oo⟩] := by
      rw [heapEq]
      exact (badHeap_buffer_frame invariant.good.live.hz
        invariant.good.live.hs i [⟨slow.put, j - oo⟩]).1
    exact ⟨result, after, j, loop, by rw [out]; exact outPtr,
      current, frame⟩

#print axioms FastInputPacket.dodist_loop_exact_frame

end Zlib.Inflate.Proofs
