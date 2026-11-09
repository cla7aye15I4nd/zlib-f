import ZlibF.Proof.«uncompr.c.local-scalar-support»
import ZlibF.Proof.«uncompr.c.compat-continuation»
import ZlibF.Math.«heap-table-updates»

namespace Zlib.Uncompr.Proof.LocalCompatPrefix
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

/-- The post-heap of the actual two allocations followed by both writes.
This description does not reorder the translated program. -/
def preparedHeap (h : Heap) (capacity n : UInt64) : Heap :=
  scalarHeap (scalarHeap h capacity) n

theorem initial_fresh (h : Heap) (fresh : Fresh h) : Fresh (initialScalar h) := by
  apply fresh.mono (by simp [initialScalar])
  intro x bound
  have different : x ≠ h.nextBlk := by change h.nextBlk + 1 ≤ x at bound; omega
  simp [initialScalar, different]

theorem initial_old_view (h : Heap) (fresh : Fresh h) (ref : BRef) (a : Array UInt8)
    (get : Space.get h ref = some a) :
    Space.get (initialScalar h) ref = some a ∧ Space.ro (initialScalar h) ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
    exact ⟨by simpa [Space.get, initialScalar, show b ≠ h.nextBlk by omega] using get,
      by simp [Space.ro, initialScalar, show b ≠ h.nextBlk by omega]⟩
  | dstate_depth b | str b | st_dist_code | st_length_code => exact ⟨get, rfl⟩

theorem initial_old_cell (h : Heap) (fresh : Fresh h) (p : BPtr) (v : UInt64)
    (cell : LengthCell h p v) : LengthCell (initialScalar h) p v := by
  constructor
  · rcases cell.1 with null | ⟨ref, off, a, ptr, get, room, value⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, (initial_old_view h fresh ref a get).1, room, value⟩
  · rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · have keep := initial_old_view h fresh ref a get
      exact Or.inr ⟨ref, off, a, ptr, keep.1, keep.2.trans ro, room⟩

/-- The first actual store happens after both real allocations. -/
theorem first_store_after_both_allocations (h : Heap) (capacity : UInt64) :
    store64 (.ref (.blk h.nextBlk) 0) capacity (initialScalar (initialScalar h)) =
      .ok ((), initialScalar (scalarHeap h capacity)) := by
  let junk : Array UInt8 := Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)
  have get : Space.get (initialScalar (initialScalar h)) (.blk h.nextBlk : BRef) = some junk := by
    simp [Space.get, initialScalar, junk]
  have write : Space.ro (initialScalar (initialScalar h)) (.blk h.nextBlk : BRef) = false := by
    simp [Space.ro, initialScalar]
  have actual := store64_slice_run (initialScalar (initialScalar h)) (.blk h.nextBlk) junk 0 capacity
    get write (by simp [junk])
  simpa [Space.put, initialScalar, scalarHeap, junk, upd_upd,
    Array.extract_empty_of_stop_le_start (Nat.le_refl 8), upd, Tbl.set_set,
    Tbl.set_comm _ (by omega : h.nextBlk ≠ h.nextBlk + 1)] using actual

/-- The original function executes both allocations before either store and
then calls the actual counted callee on this same prepared heap. -/
theorem uncompress2_to_continuation (h : Heap) (dest destLen source sourceLen : BPtr)
    (capacity n : UInt64) (fresh : Fresh h)
    (destCell : LengthCell h destLen capacity) (sourceCell : LengthCell h sourceLen n) :
    C.run (uncompress2 dest destLen source sourceLen) h =
      C.run (Zlib.Uncompr.Proof.CompatibilityContinuation.continuation dest destLen source sourceLen
        (.ref (.blk h.nextBlk) 0) (.ref (.blk (h.nextBlk + 1)) 0)) (preparedHeap h capacity n) := by
  have destRead := load64_lengthCell (initialScalar (initialScalar h)) destLen capacity
    (initial_old_cell (initialScalar h) (initial_fresh h fresh) destLen capacity
      (initial_old_cell h fresh destLen capacity destCell))
  have sourceRead := load64_lengthCell (initialScalar (scalarHeap h capacity)) sourceLen n
    (initial_old_cell (scalarHeap h capacity) (scalar_fresh h capacity fresh) sourceLen n
      (scalar_old_cell h capacity fresh sourceLen n sourceCell))
  simp only [C.run] at destRead sourceRead
  have secondAllocation : allocLocal 8 (initialScalar h) =
      .ok (.ref (.blk (h.nextBlk + 1)) 0, initialScalar (initialScalar h)) :=
    scalar_allocate (initialScalar h) (initial_fresh h fresh)
  have secondWrite : store64 (.ref (.blk (h.nextBlk + 1)) 0) n (initialScalar (scalarHeap h capacity)) =
      .ok ((), preparedHeap h capacity n) := scalar_write (scalarHeap h capacity) n
  change uncompress2 dest destLen source sourceLen h = _
  rw [Zlib.Uncompr.Proof.CompatibilityContinuation.uncompress2_continuation_source]
  simp only [bind_app, scalar_allocate h fresh, secondAllocation, destRead,
    first_store_after_both_allocations, sourceRead, secondWrite, C.run]

#print axioms first_store_after_both_allocations
#print axioms uncompress2_to_continuation
end Zlib.Uncompr.Proof.LocalCompatPrefix
