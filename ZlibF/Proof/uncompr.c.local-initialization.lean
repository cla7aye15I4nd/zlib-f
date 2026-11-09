import ZlibF.Proof.«uncompr.c.fresh-core-entry»
import ZlibF.Proof.«inflate.c.local-good»
import ZlibF.Proof.«uncompr.c.caller-frame»

/-! Fresh-only local representation on the actual initialization heaps.
Allocation success is explicit. This does not prove the subsequent decoder loop. -/
namespace Zlib.Uncompr.Proof.LocalInitialization
open C ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Loop
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem state_inv (h after : Heap) :
    StInv after (h.nextBlk + 2) (initializedState h) := by
  have win := winInv_reset2 (h := after) (initState_win (.tab h.nextBlk) after)
    (bits15 (show badBits (15 : Int32) = false by decide)) (5 : Int32)
  refine stInv_rk (wf_resetPre (wf_reset2Pre 5 15 (wf_initState (.tab h.nextBlk)))) win ?_
  simpa [reqbits_resetPre, reset2Pre] using (bits15 (show badBits (15 : Int32) = false by decide))

private theorem local_slots (h : Heap) (fresh : Fresh h) (z : ZStream) :
    UniqueFrom ({ h with
      bytes := upd h.bytes (h.nextBlk + 1) (some (junkBytes h))
      streams := upd h.streams h.nextBlk (some z)
      istates := upd h.istates (h.nextBlk + 2) (some (initializedState h))
      ro := upd h.ro (h.nextBlk + 1) false
      nextBlk := h.nextBlk + 3
      nalloc := h.nalloc + 1 } : Heap) h.nextBlk := by
  intro b lower
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := Heap.not_live.mp (fresh b lower)
  by_cases a : b = h.nextBlk <;> by_cases c : b = h.nextBlk + 1 <;>
    by_cases d : b = h.nextBlk + 2
  all_goals simp_all

/-- Every old typed-table lookup is retained, including old collisions.
These are lookup equalities, not structural equality of table storage. -/
theorem core_old_tables (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (b : Nat) (old : b < h.nextBlk) :
    (coreHeap h source dest capacity).bytes b = h.bytes b ∧
    (coreHeap h source dest capacity).words b = h.words b ∧
    (coreHeap h source dest capacity).streams b = h.streams b ∧
    (coreHeap h source dest capacity).gzheaders b = h.gzheaders b ∧
    (coreHeap h source dest capacity).dstates b = h.dstates b ∧
    (coreHeap h source dest capacity).istates b = h.istates b ∧
    (coreHeap h source dest capacity).gzstates b = h.gzstates b := by
  simp [coreHeap_eq, upd_ne _ _ _ _ (show b ≠ h.nextBlk by omega),
    upd_ne _ _ _ _ (show b ≠ h.nextBlk + 1 by omega),
    upd_ne _ _ _ _ (show b ≠ h.nextBlk + 2 by omega)]

/-- Fresh alone establishes the actual initialized local decoder representation.
No old caller table is required to be globally unique. -/
theorem initialized_local (h : Heap) (source : BPtr) (fresh : Fresh h)
    (allocation : h.allocOk h.nalloc = true) :
    C.run (inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_OK, initHeap h source) ∧
    LocalGood (initHeap h source) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (initializedStream h source) (initializedState h) ∧
    DefAlloc (initializedStream h source) := by
  refine ⟨FreshCoreEntry.initialized_run h source fresh allocation, ⟨?_, state_inv h _, ?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · exact ⟨initHeap_stream h source, initHeap_state h source, rfl, rfl,
      by simp [initializedState, resetKeepState, HEAD, SYNC], by simp [initializedStream, resetKeepStream, initStream2, initStream, Wrapper.preparedStream],
      by simp [initializedStream, resetKeepStream, initStream2, initStream, Wrapper.preparedStream]⟩
  · intro b bound live
    have above : h.nextBlk ≤ b := by simp only [initHeap_eq] at bound; omega
    have ne0 : b ≠ h.nextBlk := by simp only [initHeap_eq] at bound; omega
    have ne1 : b ≠ h.nextBlk + 1 := by simp only [initHeap_eq] at bound; omega
    have ne2 : b ≠ h.nextBlk + 2 := by simp only [initHeap_eq] at bound; omega
    apply fresh b above
    simpa only [Heap.live, initHeap_eq, upd_ne _ _ _ _ ne0,
      upd_ne _ _ _ _ ne1, upd_ne _ _ _ _ ne2] using live
  · rw [initHeap_eq]
    exact local_slots h fresh _

/-- Setting the actual output cursor retains the same local representation. -/
theorem core_local (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true) :
    LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h) ∧
    DefAlloc (coreStream h source dest capacity) := by
  have initial := (initialized_local h source fresh allocation).2.1
  refine ⟨⟨?_, state_inv h _, ?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · exact ⟨by simp [coreHeap_eq, ZStreamRef.get], by simp [coreHeap_eq], rfl, rfl,
      initial.live.mode, initial.live.zalloc, initial.live.zfree⟩
  · intro b bound live
    apply initial.fresh b bound
    have ne : b ≠ h.nextBlk := by simp only [coreHeap_eq] at bound; omega
    simpa only [Heap.live, coreHeap_eq, initHeap_eq, upd_ne _ _ _ _ ne] using live
  · rw [coreHeap_eq]
    exact local_slots h fresh _

/-- The real wrapper continuation and the local representation use exactly
one core heap, after both automatic allocations, the original guards and
length reads, real init, and output-cursor initialization. -/
theorem uncompress2_z_local_entry (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    C.run (uncompress2_z dest destLen source sourceLen) h =
      (do
        let last ← cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
          { err := Z_OK, len := n, left := capacity }
        finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last)
        (coreHeap h source dest capacity) ∧
    LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h) ∧
    DefAlloc (coreStream h source dest capacity) ∧
    Frame h (coreHeap h source dest capacity) (fun _ => False) :=
  ⟨FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity
    fresh allocation inputCell outputCell validInput validOutput,
    (core_local h source dest capacity fresh allocation).1,
    (core_local h source dest capacity fresh allocation).2,
    CallerFrame.core_frame h source dest capacity fresh⟩

/-- A caller block may have both a byte view and a word view in the model.
It lies below the fresh allocation boundary. -/
def collisionHeap : Heap :=
  { Heap.empty with bytes := upd Heap.empty.bytes 0 (some #[])
                    words := upd Heap.empty.words 0 (some #[])
                    nextBlk := 1 }

theorem collision_fresh : Fresh collisionHeap := by
  intro b bound
  have ne : b ≠ 0 := by change 1 ≤ b at bound; omega
  simp [Heap.live, collisionHeap, Heap.empty, upd_ne _ _ _ _ ne]

theorem collision_not_uniq : ¬ Uniq collisionHeap := by
  intro unique
  have atZero := unique 0
  simp [collisionHeap, Heap.empty] at atZero

/-- Concrete non-vacuity: the actual default initialization succeeds in the
presence of an old typed collision, and establishes LocalGood rather than
claiming the impossible global Good relation. -/
theorem collision_actual_initialization :
    ¬ Uniq collisionHeap ∧
    C.run (inflateInit_ (some (.tab collisionHeap.nextBlk)) (.ref (.str 57) 0) 112)
      (preparedHeap collisionHeap .null) = .ok (Z_OK, initHeap collisionHeap .null) ∧
    LocalGood (initHeap collisionHeap .null) collisionHeap.nextBlk
      (.tab collisionHeap.nextBlk) (collisionHeap.nextBlk + 2)
      (initializedStream collisionHeap .null) (initializedState collisionHeap) := by
  have initialized := initialized_local collisionHeap .null collision_fresh (by rfl)
  exact ⟨collision_not_uniq, initialized.1, initialized.2.1⟩

#print axioms uncompress2_z_local_entry
#print axioms collision_actual_initialization
#print axioms initialized_local
#print axioms core_local
#print axioms core_old_tables
end Zlib.Uncompr.Proof.LocalInitialization
