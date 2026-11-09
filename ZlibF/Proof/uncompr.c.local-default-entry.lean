import ZlibF.Proof.«uncompr.c.local-initialization»
import ZlibF.Proof.«inflate.c.local-default-state»

/-! Actual initialized decoder fields without old caller uniqueness. -/
namespace Zlib.Uncompr.Proof.LocalDefaultEntry
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper
set_option autoImplicit false

/-- The actual core heap satisfies every initialized decode clause.
The object-size premise concerns separate byte objects, not total stream length. -/
theorem core_decode (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true)
    (globals : LibraryGlobals h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    LocalDecodeJ (coreHeap h source dest capacity) h.nextBlk
      (.tab h.nextBlk) (h.nextBlk + 2) (coreStream h source dest capacity) (initializedState h) := by
  have current := (LocalInitialization.core_local h source dest capacity fresh allocation).1
  have head : (initializedState h).mode = HEAD := rfl
  have fit : ZlibF.PlatformMemory.ByteObjectsFit (coreHeap h source dest capacity) := by
    apply (prepared_platform h platform source).of_storage_eq
    · simp only [coreHeap_eq, preparedHeap, localHeap]
    · simp only [coreHeap_eq, preparedHeap, localHeap]
    · simp only [coreHeap_eq, preparedHeap, localHeap]
  refine ⟨current, dataTableInvariant_head head,
    dataPendingInvariant_head (by rfl) head, ?_, ?_, ?_, ?_, ?_, rfl,
    Or.inl head, ?_, ?_, fit⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
    decide
  · rfl
  · exact Or.inr (Or.inr rfl)
  · rintro (active | active) <;> rw [head] at active <;> contradiction
  · change (coreHeap h source dest capacity).static = _
    simpa only [coreHeap_eq, LibraryGlobals] using globals

/-- Reset requests and the unread-header phase are the actual initialized fields. -/
theorem core_requested (h : Heap) :
    (initializedState h).reqbits = 15 ∧
    ((initializedState h).reqwrap = 1 ∨ (initializedState h).reqwrap = 5) ∧
    (initializedState h).mode = HEAD := ⟨rfl, Or.inr rfl, rfl⟩

#print axioms core_decode
#print axioms core_requested
end Zlib.Uncompr.Proof.LocalDefaultEntry
