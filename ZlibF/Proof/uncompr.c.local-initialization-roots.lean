import ZlibF.Proof.«uncompr.c.local-initialization»
import ZlibF.Proof.«inflate.c.local-end»

/-! The ages of private roots come from the real wrapper allocations and init.
No age or local decoder representation is assumed of caller storage. -/
namespace Zlib.Uncompr.Proof.LocalInitialization
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open ZlibF.Spec.Public Zlib.Uncompr.Proof.Wrapper
set_option autoImplicit false

/-- Actual initialization puts the stream at the old allocation boundary,
the state two automatic allocations later, and leaves the window NULL. -/
theorem initialized_roots (h : Heap) :
    LocalRoots h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) (initializedState h) := by
  refine ⟨?_, by omega, ?_⟩
  · intro b root
    change b = h.nextBlk at root
    omega
  · intro w pointer
    simp [initializedState, resetKeepState, resetPre, reset2Pre, initState,
      InflateState.zeroed, InflateState.garbage] at pointer

/-- Output-cursor setup keeps exactly the same state and root ages. -/
theorem core_roots (h : Heap) :
    LocalRoots h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) (initializedState h) :=
  initialized_roots h

/-- Both actual init execution and its new local root-age relation are produced
on the same returned heap, from Fresh and the real successful allocator result. -/
theorem initialized_local_roots (h : Heap) (source : BPtr) (fresh : Fresh h)
    (allocation : h.allocOk h.nalloc = true) :
    C.run (inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_OK, initHeap h source) ∧
    LocalGood (initHeap h source) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (initializedStream h source) (initializedState h) ∧
    LocalRoots h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) (initializedState h) ∧
    DefAlloc (initializedStream h source) := by
  have actual := initialized_local h source fresh allocation
  exact ⟨actual.1, actual.2.1, initialized_roots h, actual.2.2⟩

/-- The real core heap supplies the complete local input to inflateEnd. -/
theorem core_local_roots (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true) :
    LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h) ∧
    LocalRoots h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) (initializedState h) ∧
    DefAlloc (coreStream h source dest capacity) := by
  have actual := core_local h source dest capacity fresh allocation
  exact ⟨actual.1, core_roots h, actual.2⟩

#print axioms initialized_local_roots
#print axioms core_local_roots
end Zlib.Uncompr.Proof.LocalInitialization
