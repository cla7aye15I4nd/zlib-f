import ZlibF.Proof.«inflate.c.copy-window-J»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A successful actual copy keeps J for both stream records. The source
table-origin premise is internal and still needs full-history producers. -/
theorem inflateCopy_origin_success_both_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (origin : CopyTableOrigin zs s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : s.window ≠ .null → h.allocOk (h.nalloc + 1) = true) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      DefaultStateJ after source zs z s := by
  by_cases window : s.window = .null
  · rcases origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound,
        distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry invariant.good dynamic
      obtain ⟨after, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_dynamic_no_window_exec invariant.good allocator destGet
          different first window nextPtr nextBound dynamic distPtr distBound
      rw [copiedEq] at heapEq
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff distOff .null s
      have destination := copiedGeneric_no_window_J invariant destGet
        (Or.inl dynamic) nextBound distBound (fun _ => distPtr) window
      have original := copiedGeneric_no_window_source_J invariant destGet
        different (Or.inl dynamic) nextPtr nextBound distBound
        (fun _ => distPtr) window
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact destination
      · rw [heapEq]
        exact original
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
      obtain ⟨after, run, _, _, _, copied, _, copiedEq, heapEq⟩ :=
        inflateCopy_fixed_no_window_exec invariant.good allocator destGet
          different first window nextPtr nextBound fixed
      rw [copiedEq] at heapEq
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff 0 .null s
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedGeneric_no_window_J invariant destGet
        (Or.inr fixed) nextBound (by decide : 0 ≤ 1443)
        impossible window
      have original := copiedGeneric_no_window_source_J invariant destGet
        different (Or.inr fixed) nextPtr nextBound
        (by decide : 0 ≤ 1443) impossible window
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact destination
      · rw [heapEq]
        exact original
  · rcases origin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound,
        distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry invariant.good dynamic
      obtain ⟨after, run, sourceGet, stateGet, _, copiedGet,
        sourceArray, heapEq⟩ :=
        inflateCopy_dynamic_window_exec invariant.good allocator destGet
          different first (second window) window nextPtr nextBound dynamic
          distPtr distBound
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff distOff
        (.ref (.blk (h.nextBlk + 1)) 0) s
      have destination := copiedWindowHeap_J sourceArray invariant destGet
        (Or.inl dynamic) nextBound distBound (fun _ => distPtr)
      have sourceCanonical : source.get
          (copiedWindowHeap h dest z s copiedState sourceArray) = some z := by
        rw [← heapEq]
        exact sourceGet
      have stateCanonical :
          (copiedWindowHeap h dest z s copiedState sourceArray).istates zs = some s := by
        rw [← heapEq]
        exact stateGet
      have original := copiedWindowHeap_source_J sourceArray invariant
        (Or.inl dynamic) nextPtr (fun _ => distPtr)
        sourceCanonical stateCanonical destination
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact destination
      · rw [heapEq]
        exact original
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
      obtain ⟨after, run, sourceGet, stateGet, _, copiedGet,
        sourceArray, heapEq⟩ :=
        inflateCopy_fixed_window_exec invariant.good allocator destGet
          different first (second window) window nextPtr nextBound fixed
      let copiedState := copiedGeneric dest zs h.nextBlk nextOff 0
        (.ref (.blk (h.nextBlk + 1)) 0) s
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      have destination := copiedWindowHeap_J sourceArray invariant destGet
        (Or.inr fixed) nextBound (by decide : 0 ≤ 1443) impossible
      have sourceCanonical : source.get
          (copiedWindowHeap h dest z s copiedState sourceArray) = some z := by
        rw [← heapEq]
        exact sourceGet
      have stateCanonical :
          (copiedWindowHeap h dest z s copiedState sourceArray).istates zs = some s := by
        rw [← heapEq]
        exact stateGet
      have original := copiedWindowHeap_source_J sourceArray invariant
        (Or.inr fixed) nextPtr impossible
        sourceCanonical stateCanonical destination
      refine ⟨after, copiedState, run, ?_, ?_⟩
      · rw [heapEq]
        exact destination
      · rw [heapEq]
        exact original

#print axioms inflateCopy_origin_success_both_J
end Zlib.Inflate.Proofs
