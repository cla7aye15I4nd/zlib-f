import ZlibF.Proof.«inflate.c.copy-window-heap»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A windowed dynamic-table source is copied by the actual translated C,
including bounded nonzero dynamic cursors and the byte-for-byte window copy. -/
theorem inflateCopy_dynamic_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (dynamic : s.lencode = .ref (.istate_codes zs) 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨nextOff, distOff, nextPtr, nextBound,
    distPtr, distBound, _, _⟩ :=
    CopyTableOrigin.dynamic_geometry invariant.good dynamic
  obtain ⟨after, run, sourceGet, sourceState, _, copiedState,
    sourceArray, heapEq⟩ :=
    inflateCopy_dynamic_window_exec invariant.good allocator destGet
      different first second window nextPtr nextBound dynamic distPtr distBound
  let copied := copiedGeneric dest zs h.nextBlk nextOff distOff
    (.ref (.blk (h.nextBlk + 1)) 0) s
  have nextJ : DefaultStateJ
      (copiedWindowHeap h dest z s copied sourceArray) dest h.nextBlk
      { z with state := some (.inflate h.nextBlk) } copied :=
    copiedWindowHeap_J sourceArray invariant destGet (Or.inl dynamic)
      nextBound distBound (fun _ => distPtr)
  refine ⟨after, copied, run, ?_, sourceGet, sourceState⟩
  rw [heapEq]
  exact nextJ

/-- A windowed fixed-table source preserves its static table pointers while
the actual translated C relocates its `next` cursor and copies the window. -/
theorem inflateCopy_fixed_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (fixed : s.lencode = .ref .st_lenfix 0 ∧
      s.distcode = .ref .st_distfix 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
  obtain ⟨after, run, sourceGet, sourceState, _, copiedState,
    sourceArray, heapEq⟩ :=
    inflateCopy_fixed_window_exec invariant.good allocator destGet
      different first second window nextPtr nextBound fixed
  let copied := copiedGeneric dest zs h.nextBlk nextOff 0
    (.ref (.blk (h.nextBlk + 1)) 0) s
  have nextJ : DefaultStateJ
      (copiedWindowHeap h dest z s copied sourceArray) dest h.nextBlk
      { z with state := some (.inflate h.nextBlk) } copied :=
    copiedWindowHeap_J sourceArray invariant destGet (Or.inr fixed)
      nextBound (by decide : 0 ≤ 1443)
      (by intro impossible; cases fixed.1.symm.trans impossible)
  refine ⟨after, copied, run, ?_, sourceGet, sourceState⟩
  rw [heapEq]
  exact nextJ

/-- Internal successful-copy closure for every source with the separately
established table-origin fact. This does not assert public history closure. -/
theorem inflateCopy_origin_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (origin : CopyTableOrigin zs s) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  rcases origin with dynamic | fixed
  · exact inflateCopy_dynamic_window_J invariant allocator destGet
      different first second window dynamic
  · exact inflateCopy_fixed_window_J invariant allocator destGet
      different first second window fixed

/-- Complete successful allocation path of the translated `inflateCopy`
under the internal source-origin fact. The second allocation is needed only
when a source window exists. The source stream and state records are retained. -/
theorem inflateCopy_origin_success_J
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
      source.get after = some z ∧ after.istates zs = some s := by
  by_cases window : s.window = .null
  · exact inflateCopy_origin_no_window_J invariant allocator destGet
      different first window origin
  · exact inflateCopy_origin_window_J invariant allocator destGet
      different first (second window) window origin

#print axioms inflateCopy_origin_window_J
#print axioms inflateCopy_origin_success_J
end Zlib.Inflate.Proofs
