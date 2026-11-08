import ZlibF.Proof.«inflate.c.fast-view-dist-linked-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Actual distance lookup and its one- or two-pass loop retain one cursor count and a bit budget through base, linked, invalid, and bad-distance exits. -/
theorem FastInputPacket.dodist_loop_bit_budget
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
    ∃ result after pulled,
      pulled ≤ 2 ∧
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨rootBound, rootWidthBound, classes⟩ :=
    dist_table_root_cases safe root
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  rw [rootEq] at rootWidthBound classes
  have rootFitsSlow : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      l.bits.toNat := by rw [packet.bits]; exact rootFitsSlow
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
    obtain ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩ :=
      packet.dodist_base_leaf_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFitsSlow rootWidthBound
        baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    obtain ⟨pulled, bound, cursor, bits⟩ :=
      Zlib.Inffast.Proofs.dodist_base_two_pull_bit_ledger
        rootLoad rootWidthBound rootFits baseBool extras
        (by simpa only [C.run] using run)
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
    exact ⟨result, after, pulled, bound, loop, cursor, by omega⟩
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, result, after, pulled, bound,
      firstRun, secondRun, againD, noAgain, cursor, bits⟩ :=
      packet.dodist_linked_leaf_bit_budget invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr dcodePtr codesGet safe root rootLink held left
        avail length outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
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
    exact ⟨result, after, pulled, bound, loop, cursor, bits⟩
  · have nonbase :
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
      broke, noAgain, invalidCursor, out, finalPacket,
      finalState, finalBuffers, sizes, source⟩ :=
      packet.dodist_invalid_leaf_default_state invariant
        buffers streamPtr statePtr herePtr codesGet
        rootBound rootFitsSlow rootWidthBound nonbase notLink
    obtain ⟨cursor, bits⟩ :=
      Zlib.Inffast.Proofs.dodist_nonbase_bit_ledger
        rootLoad rootFits rootWidthBound nonbase
        (by simpa only [C.run] using run)
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    exact ⟨result, after, 0, by omega, loop,
      by simpa only [inputAdvance_zero] using cursor, by omega⟩

#print axioms FastInputPacket.dodist_loop_bit_budget
/-- Any observed successful return of this actual distance loop has the same cursor and bit budget. -/
theorem FastInputPacket.dodist_loop_result_bit_budget
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {result : Zlib.Inffast.L} {after : Heap}
    (run : C.run (cdoWhile (Zlib.Inffast.dodist c)
      (fun q => pure (q.againD, q)) l) h = .ok (result, after)) :
    ∃ pulled, pulled ≤ 2 ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨found, foundAfter, pulled, bound, foundRun,
    cursor, bits⟩ :=
    packet.dodist_loop_bit_budget invariant buffers streamPtr
      statePtr whaveEq wsizeEq wnextEq windowEq herePtr dcodePtr
      codesGet safe root held left avail length outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current beginLe
      span guard
  have same : (result, after) = (found, foundAfter) :=
    Except.ok.inj (run.symm.trans foundRun)
  have resultEq : result = found := congrArg Prod.fst same
  subst found
  exact ⟨pulled, bound, cursor, bits⟩

#print axioms FastInputPacket.dodist_loop_result_bit_budget
end Zlib.Inflate.Proofs
