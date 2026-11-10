import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-one-byte-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-one-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The complete translated distance loop retains at most 30 held bits
whenever it returns a result that can continue decoding. -/
theorem FastInputPacket.dodist_loop_one_byte_bits_default_state
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
    ∃ used slowNext result after,
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h =
          .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: rest).drop used) result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨used, _, slowNext, result, after, _, _, run,
    _, finalPacket, _, _, _, _, _⟩ :=
    packet.dodist_loop_one_byte_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr dcodePtr codesGet safe root held left avail
      length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  change (cdoWhile (Zlib.Inffast.dodist c)
    (fun q => pure (q.againD, q)) l) h =
      .ok (result, after) at run
  obtain ⟨rootBound, rootWidthBound, classes⟩ :=
    dist_table_root_cases safe root
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
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
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
      have baseHeld : 5 + codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat := by omega
      obtain ⟨_, slowLeaf, result0, after0, _, leafRun,
        leafPost, _, _, _, _, _, leafBound⟩ :=
        packet.dodist_base_leaf_one_byte_bits_default_state invariant
          buffers streamPtr statePtr whaveEq wsizeEq wnextEq
          windowEq herePtr codesGet rootBound rootFits
          rootWidthBound baseHeld baseBool extras bitsBound left avail
          length outPtr outputPtr begPtr endPtr outputGet
          outputWrite outputSize current beginLe span guard
      have noAgain := Zlib.Inffast.Proofs.dodist_base_againD_false
        rootLoad rootWidthBound baseBool leafRun
      have cond :
          (fun q : Zlib.Inffast.L =>
            (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
            result0 after0 = .ok ((false, result0), after0) := by
        simp [noAgain]
      have loop0 := Zlib.Inffast.Proofs.cdoWhile_one
        (body := Zlib.Inffast.dodist c)
        (cond := fun q => (pure (q.againD, q) :
          M (Bool × Zlib.Inffast.L))) leafRun cond
      rw [run] at loop0
      cases loop0
      have sameBits : slowNext.bits = slowLeaf.bits :=
        finalPacket.bits.symm.trans leafPost.1.bits
      rw [sameBits]
      exact leafBound
    · have rootLink : DistLink
          (codes.getD (baseOff + rootSlice) default) := by
        rw [rootEq]
        exact ⟨linkClass.1, linkClass.2.1⟩
      obtain ⟨linked, slice, firstRun, againD,
        sliceBound, here, leaf, _, _, result1, after1,
        _, secondRun, _, _, _, _, _⟩ :=
        packet.dodist_linked_leaf_one_byte_frame_default_state
          invariant buffers streamPtr statePtr whaveEq
          wsizeEq wnextEq windowEq herePtr dcodePtr
          codesGet safe root rootLink held left avail
          length outPtr outputPtr begPtr endPtr outputGet
          outputWrite outputSize current beginLe span guard
      obtain ⟨linked0, _, slowLeaf, result0, after0,
        firstRun0, secondRun0, leafPacket, bound0⟩ :=
        packet.dodist_linked_leaf_one_byte_bits_default_state
          invariant buffers streamPtr statePtr whaveEq
          wsizeEq wnextEq windowEq herePtr dcodePtr
          codesGet safe root rootLink held bitsBound left
          avail length outPtr outputPtr begPtr endPtr
          outputGet outputWrite outputSize current beginLe
          span guard
      rw [firstRun] at firstRun0
      cases firstRun0
      let targetIndex : Nat := baseOff +
        codes[baseOff + rootSlice].val.toNat + slice
      have targetBound : targetIndex < codes.size := by
        have target := dist_table_link_target safe root rootLink
          (by simpa only [rootEq] using sliceBound)
        simpa only [rootEq, targetIndex] using target.1
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
      have noAgain : result0.againD = false := by
        rcases targetLeaf.2 with base | invalid
        · have baseBool :
              (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
                true := by
            rw [Zlib.Inffast.Proofs.mask16]
            simp [base.1]
          exact Zlib.Inffast.Proofs.dodist_base_againD_false
            targetLoad targetWidth baseBool secondRun0
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
            targetLoad targetWidth notBase notLink secondRun0
      have condFirst :
          (fun q : Zlib.Inffast.L =>
            (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
            linked h = .ok ((true, linked), h) := by
        simp [againD]
      have condSecond :
          (fun q : Zlib.Inffast.L =>
            (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
            result0 after0 = .ok ((false, result0), after0) := by
        simp [noAgain]
      have loop0 := Zlib.Inffast.Proofs.cdoWhile_two
        (body := Zlib.Inffast.dodist c)
        (cond := fun q => (pure (q.againD, q) :
          M (Bool × Zlib.Inffast.L)))
        firstRun condFirst secondRun0 condSecond
      rw [run] at loop0
      cases loop0
      have sameBits : slowNext.bits = slowLeaf.bits :=
        finalPacket.bits.symm.trans leafPacket.bits
      rw [sameBits]
      exact bound0 notBroken
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
      obtain ⟨_, after0, result0, _, invalidRun, _,
        broke0, noAgain, _, _, _, _, _, _, _⟩ :=
        packet.dodist_invalid_leaf_default_state invariant
          buffers streamPtr statePtr herePtr codesGet
          rootBound rootFits rootWidthBound notBase notLink
      have cond :
          (fun q : Zlib.Inffast.L =>
            (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
            result0 after0 = .ok ((false, result0), after0) := by
        simp [noAgain]
      have loop0 := Zlib.Inffast.Proofs.cdoWhile_one
        (body := Zlib.Inffast.dodist c)
        (cond := fun q => (pure (q.againD, q) :
          M (Bool × Zlib.Inffast.L))) invalidRun cond
      rw [run] at loop0
      cases loop0
      rw [broke0] at notBroken
      cases notBroken
  exact ⟨used, slowNext, result, after,
    run, finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
