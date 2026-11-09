import ZlibF.Proof.«uncompr.c.local-default-entry»
import ZlibF.Proof.«uncompr.c.local-initialization-roots»
import ZlibF.Proof.«uncompr.c.valid-entry-witness»

/-! The full local history relation at the actual wrapper core boundary. -/
namespace Zlib.Uncompr.Proof.LocalDefaultEntry
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

/-- All decoder history and root-age fields come from the same real initialization. -/
theorem core_state (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true)
    (globals : LibraryGlobals h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    LocalStateJ (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk)
      (h.nextBlk + 2) (coreStream h source dest capacity) (initializedState h) :=
  ⟨core_decode h source dest capacity fresh allocation globals platform,
    rfl, Or.inr rfl, Or.inl rfl, LocalInitialization.core_roots h⟩

/-- The actual whole wrapper prefix reaches that same local history relation.
There is no precondition on uniqueness of any pre-existing caller object. -/
theorem uncompress2_z_state_entry (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true)
    (globals : LibraryGlobals h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    C.run (Zlib.Uncompr.uncompress2_z dest destLen source sourceLen) h =
      (do
        let last ← cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
          { err := Z_OK, len := n, left := capacity }
        finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last)
        (coreHeap h source dest capacity) ∧
    LocalStateJ (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h) ∧
    DefAlloc (coreStream h source dest capacity) ∧
    Frame h (coreHeap h source dest capacity) (fun _ => False) := by
  have entry := LocalInitialization.uncompress2_z_local_entry h source dest sourceLen destLen n capacity
    fresh allocation inputCell outputCell validInput validOutput
  exact ⟨entry.1, core_state h source dest capacity fresh allocation globals platform,
    entry.2.2.1, entry.2.2.2⟩

/-- Add an old typed collision to an existing valid caller. Its byte views,
static image and successful allocator result are retained. -/
def collidingEntryHeap : Heap :=
  { ValidEntryWitness.entryHeap with words := upd ValidEntryWitness.entryHeap.words 1 (some #[]) }

private theorem colliding_fresh : Fresh collidingEntryHeap := by
  intro b lower live
  have above : 3 ≤ b := lower
  have different : b ≠ 1 := by omega
  apply ValidEntryWitness.entry_fresh b lower
  simpa only [Heap.live, collidingEntryHeap, upd_ne _ _ _ _ different] using live

private theorem colliding_platform : ZlibF.PlatformMemory.ByteObjectsFit collidingEntryHeap :=
  ValidEntryWitness.entry_platform.of_storage_eq rfl rfl rfl

private theorem colliding_cell (b : Nat) (which : b = 1 ∨ b = 2) :
    LengthCell collidingEntryHeap (.ref (.blk b) 0) 0 :=
  ValidEntryWitness.entry_cell b which

/-- A non-unique caller concretely inhabits the full local entry relation.
This is an actual initialization witness, not a successful compressed-stream witness. -/
theorem colliding_state_entry :
    ¬ Uniq collidingEntryHeap ∧
    LocalStateJ (coreHeap collidingEntryHeap .null .null 0) collidingEntryHeap.nextBlk
      (.tab collidingEntryHeap.nextBlk) (collidingEntryHeap.nextBlk + 2)
      (coreStream collidingEntryHeap .null .null 0) (initializedState collidingEntryHeap) := by
  refine ⟨?_, core_state collidingEntryHeap .null .null 0 colliding_fresh (by rfl) rfl colliding_platform⟩
  intro unique
  have bound := unique 1
  simp [collidingEntryHeap, ValidEntryWitness.entryHeap, ValidEntryWitness.firstHeap,
    witnessHeap, Heap.empty, cnt] at bound

/-- The same non-unique caller satisfies the actual scalar guards and reaches
that core execution, with all original caller allocations framed. -/
theorem colliding_wrapper_entry :
    C.run (Zlib.Uncompr.uncompress2_z .null (.ref (.blk 2) 0) .null (.ref (.blk 1) 0))
      collidingEntryHeap =
      (do
        let last ← cdoWhile (loopBody (some (.tab collidingEntryHeap.nextBlk))) loopCondition
          { err := Z_OK, len := 0, left := 0 }
        finish (some (.tab collidingEntryHeap.nextBlk))
          (.ref (.blk (collidingEntryHeap.nextBlk + 1)) 0)
          (.ref (.blk 2) 0) (.ref (.blk 1) 0) last)
        (coreHeap collidingEntryHeap .null .null 0) :=
  (uncompress2_z_state_entry collidingEntryHeap .null .null (.ref (.blk 1) 0) (.ref (.blk 2) 0)
    0 0 colliding_fresh (by rfl) rfl colliding_platform
    (colliding_cell 1 (Or.inl rfl)) (colliding_cell 2 (Or.inr rfl))
    (fun _ => rfl) (fun _ => rfl)).1

#print axioms core_state
#print axioms uncompress2_z_state_entry
#print axioms colliding_state_entry
#print axioms colliding_wrapper_entry
end Zlib.Uncompr.Proof.LocalDefaultEntry
