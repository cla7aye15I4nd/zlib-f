import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-linked»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-loop-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-loop-one-byte-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

theorem FastInputPacket.dodist_loop_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (cdoWhile (Zlib.Inffast.dodist c)
      (fun q => pure (q.againD, q)) l) h = .ok (value, finalHeap)) :
    FastExecEffect h finalHeap r zs z s slow dest j l value 2 258 := by
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
      run, post, source⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.dodist_base_leaf_local_state packet) invariant buffers
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
    have effect :=
      Zlib.Inflate.Local.FastInputPacket.dodist_base_leaf_effect packet invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound
        baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard run
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, result, after, firstRun, againD, secondRun, noAgain, effect⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dodist_linked_leaf_effect packet invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
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
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect
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
      (Zlib.Inflate.Local.FastInputPacket.dodist_invalid_leaf_local_state packet) invariant
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
    have effect := Zlib.Inflate.Local.FastInputPacket.dodist_invalid_leaf_effect packet invariant
      buffers streamPtr statePtr herePtr codesGet rootBound rootFits rootWidthBound
      notBase notLink outPtr run
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect.widen (by omega) (by omega)

#print axioms FastInputPacket.dodist_loop_effect

theorem FastInputPacket.dodist_loop_one_byte_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (cdoWhile (Zlib.Inffast.dodist c)
      (fun q => pure (q.againD, q)) l) h = .ok (value, finalHeap)) :
    FastExecEffect h finalHeap r zs z s slow dest j l value 1 258 := by
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
      run, post, source⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.dodist_base_leaf_one_byte_local_state packet) invariant buffers
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
    have effect :=
      Zlib.Inflate.Local.FastInputPacket.dodist_base_leaf_one_byte_effect packet invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound (by omega)
        baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard run
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, result, after, firstRun, againD, secondRun, noAgain, effect⟩ :=
      Zlib.Inflate.Local.FastInputPacket.dodist_linked_leaf_one_byte_effect packet invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
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
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect
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
      (Zlib.Inflate.Local.FastInputPacket.dodist_invalid_leaf_local_state packet) invariant
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
    have effect := Zlib.Inflate.Local.FastInputPacket.dodist_invalid_leaf_effect packet invariant
      buffers streamPtr statePtr herePtr codesGet rootBound rootFits rootWidthBound
      notBase notLink outPtr run
    have same := Prod.mk.inj (Except.ok.inj (loop.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect.widen (by omega) (by omega)

#print axioms FastInputPacket.dodist_loop_one_byte_effect

end Zlib.Inflate.Local
