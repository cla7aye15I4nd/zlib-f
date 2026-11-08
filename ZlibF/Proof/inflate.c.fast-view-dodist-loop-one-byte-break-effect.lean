import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-one-byte-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-one-byte-break-effect»
import ZlibF.Proof.«inffast.c.again-d»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual distance loop takes one root pass or a root link and one leaf
pass, reading at most one byte when it starts with twenty held bits. -/
theorem FastInputPacket.dodist_loop_one_byte_break_effect
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
    ∃ used consumed slowNext result after,
      used ≤ 1 ∧ consumed ≤ 28 ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h =
          .ok (result, after) ∧
      result.againD = false ∧
      FastInputPacket after slowNext
        ((first :: rest).drop used) result ∧
      DispatchBuffers after r slowNext
        ((first :: rest).drop used) ∧
      ByteViewSizes h after ∧
      stream slowNext ((first :: rest).drop used) =
        (stream slow (first :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: rest).drop used) result
        dest output j l.len.toNat ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i ∧
         DefaultStateJ after r zs
           { z with msg := .ref (.str i) 0 }
           { s with mode := BAD }) ∧
      (result.broke = false →
        slowNext.put = slow.put ∧
        slowNext.left = slow.left ∧
        slowNext.out_ = slow.out_ ∧
        slowNext.next = inputAdvance slow.next used) ∧
      ((result.broke = l.broke ∧
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
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
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extras :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 15).toNat ≤
          13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨used, slowNext, result, after, usedBound,
      run, post, source, putFrame, leftFrame, outFrame,
      nextFrame, effect⟩ :=
      packet.dodist_base_leaf_one_byte_break_effect invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound (by omega)
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
    refine ⟨used,
      codes[baseOff + rootSlice].bits.toNat +
        (codes[baseOff + rootSlice].op.toUInt32 &&& 15).toNat,
      slowNext, result, after, usedBound, by omega,
      loop, noAgain, post.1, post.2.1,
      post.2.2.1, ?_, Or.inl post,
      fun _ => ⟨putFrame, leftFrame, outFrame, nextFrame⟩,
      effect⟩
    simpa only [List.drop_drop] using source
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, slice, firstRun, againD,
      sliceBound, here, leaf, used, slowNext,
      result, after, usedBound, secondRun,
      finalPacket, finalBuffers, sizes, outcome,
      frameAfter, effect⟩ :=
      packet.dodist_linked_leaf_one_byte_break_effect invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
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
    have targetEqNorm : codes.getD
        (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
        default =
        codes[baseOff +
          (codes[baseOff + rootSlice].val.toNat + slice)] := by
      simpa only [targetIndex, Nat.add_assoc] using targetEq
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
    have noAgain : result.againD = false := by
      rcases targetLeaf.2 with base | invalid
      · have baseBool :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              true := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [base.1]
        exact Zlib.Inffast.Proofs.dodist_base_againD_false
          targetLoad targetWidth baseBool secondRun
      · have notBase :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              false := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [invalid.1]
        have notLink :
            (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
              false := by
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
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L)))
      firstRun condFirst secondRun condSecond
    rcases outcome with ⟨extra, extraBound, post, source⟩ |
      ⟨i, broke, _, heapEq, finalState, source⟩
    · refine ⟨used,
        codes[baseOff + rootSlice].bits.toNat +
          (codes[targetIndex].bits.toNat + extra),
        slowNext, result, after, usedBound, by omega,
        loop, noAgain, finalPacket, finalBuffers, sizes,
        ?_, Or.inl post, frameAfter, effect⟩
      simpa only [rootEq, targetIndex, targetEqNorm,
        List.drop_drop, Nat.add_assoc] using source
    · refine ⟨used,
        codes[baseOff + rootSlice].bits.toNat +
          codes[targetIndex].bits.toNat,
        slowNext, result, after, usedBound, by omega,
        loop, noAgain, finalPacket, finalBuffers, sizes,
        ?_, Or.inr ⟨i, broke, heapEq, finalState⟩,
        frameAfter, effect⟩
      simpa only [rootEq, targetIndex, targetEq,
        List.drop_drop] using source
  · have notBase :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLink :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, noAgain, _, _, finalPacket, finalState,
      finalBuffers, sizes, source⟩ :=
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
    have frame : result.broke = false →
        slowNext.put = slow.put ∧ slowNext.left = slow.left ∧
        slowNext.out_ = slow.out_ ∧
        slowNext.next = inputAdvance slow.next 0 := by
      intro notBroken
      rw [broke] at notBroken
      cases notBroken
    exact ⟨0, codes[baseOff + rootSlice].bits.toNat,
      slowNext, result, after, by omega, by omega,
      loop, noAgain, by simpa using finalPacket,
      by simpa using finalBuffers, sizes,
      by simpa [List.drop_zero] using source,
      Or.inr ⟨i, broke, heapEq, finalState⟩,
      frame, Or.inr ⟨i, broke, heapEq⟩⟩

#print axioms FastInputPacket.dodist_loop_one_byte_break_effect

end Zlib.Inflate.Proofs
