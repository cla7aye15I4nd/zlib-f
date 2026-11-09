import ZlibF.Proof.«uncompr.c.local-state-entry»
import ZlibF.Proof.«inflate.c.local-operations»
import ZlibF.Proof.«uncompr.c.wrapper-ranges»

namespace Zlib.Uncompr.Proof.LocalWrapperRanges
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.WrapperRanges
set_option autoImplicit false

private theorem root_lt (h : Heap) (fresh : Fresh h) (ref : BRef) (off x : Nat) (a : Array UInt8)
    (get : Space.get h ref = some a) (root : ByteRoot (.ref ref off) x) : x < h.nextBlk := by
  cases ref with
  | blk b =>
    change x = b at root
    subst x
    exact fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
  | dstate_depth b =>
    change x = b at root
    subst x
    cases state : h.dstates b with
    | none => simp [Space.get, state] at get
    | some state => exact fresh.lt (by simp [Heap.live, state])
  | str i => cases root
  | st_dist_code => cases root
  | st_length_code => cases root

/-- All actual old caller ranges lie outside the newly initialized decoder graph. -/
theorem core_old_range (h : Heap) (fresh : Fresh h) (source dest p : BPtr) (capacity : UInt64)
    (n : Nat) (xs : List UInt8) (write : Bool)
    (good : LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (readable : Bytes h p n xs) (writable : write = true → Writable h p n) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) p n write := by
  rcases readable with null | ⟨ref, off, a, ptr, get, fit, values⟩
  · exact Or.inl null.1
  · subst p
    refine Or.inr ⟨⟨xs, Or.inr ⟨ref, off, a, rfl, core_get h fresh source dest capacity ref a get, fit, values⟩⟩,
      ?_, ?_⟩
    · intro writing
      rcases writable writing with null | ⟨ref', off', a', ptr, get', ro, fit'⟩
      · cases null.1
      · cases ptr
        exact Or.inr ⟨ref, off, a', rfl, core_get h fresh source dest capacity ref a' get',
          (core_ro h fresh source dest capacity ref a' get').trans ro, fit'⟩
    · intro x root owned
      have below := root_lt h fresh ref off x a get root
      rw [good.streamOwned_iff] at owned
      rcases owned with decoder | window
      · omega
      · rw [initial_window_null] at window
        cases window

/-- The real local reserved field supplies a writable nonnull range, including
when NULL+zero output is normalized to it. It is outside the decoder-owned state. -/
theorem core_reserved_range (h : Heap) (source dest : BPtr) (capacity : UInt64) (n : Nat) (write : Bool)
    (good : LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)) (bound : n ≤ 8) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (.ref (.blk (h.nextBlk + 1)) 0) n write := by
  have get : Space.get (coreHeap h source dest capacity) (.blk (h.nextBlk + 1) : BRef) = some (junkBytes h) := by
    simp [Space.get, coreHeap_eq]
  have fit : 0 + n ≤ (junkBytes h).size := by simpa [junkBytes] using bound
  refine Or.inr ⟨⟨(junkBytes h).toList.take n, Or.inr ⟨.blk (h.nextBlk + 1), 0, junkBytes h,
    rfl, get, fit, by simp⟩⟩, ?_, ?_⟩
  · intro _
    exact Or.inr ⟨.blk (h.nextBlk + 1), 0, junkBytes h, rfl, get, by simp [Space.ro, coreHeap_eq], fit⟩
  · intro x root owned
    change x = h.nextBlk + 1 at root
    rw [good.streamOwned_iff] at owned
    rcases owned with decoder | window
    · omega
    · rw [initial_window_null] at window
      cases window

theorem core_output_range (h : Heap) (fresh : Fresh h) (source dest : BPtr) (capacity : UInt64)
    (good : LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (writable : Writable h dest capacity.toNat) (valid : dest = .null → capacity = 0) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) (normalizedDest h dest capacity) capacity.toNat true := by
  by_cases null : dest = .null
  · have zero := valid null
    simpa [normalizedDest, null, zero] using core_reserved_range h source dest capacity 0 true good (by omega)
  · obtain ⟨xs, readable⟩ := writable_bytes h dest capacity.toNat writable
    have range := core_old_range h fresh source dest dest capacity capacity.toNat xs true good readable (fun _ => writable)
    simpa [normalizedDest, null] using range

theorem core_remaining_buffers (h : Heap) (fresh : Fresh h) (source dest : BPtr) (n capacity : UInt64)
    (xs : List UInt8)
    (good : LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (valid : dest = .null → capacity = 0) :
    RemainingBuffers (coreHeap h source dest capacity) h.nextBlk (coreStream h source dest capacity)
      { err := Z_OK, len := n, left := capacity } := by
  have input := core_old_range h fresh source dest source capacity n.toNat xs false good readable (by simp)
  have output := core_output_range h fresh source dest capacity good writable valid
  have separation : Separate source n.toNat (normalizedDest h dest capacity) capacity.toNat := by
    by_cases null : dest = .null
    · simp [Separate, normalizedDest, null, valid null]
    · simpa [normalizedDest, null] using separate
  exact ⟨input, output, separation⟩

theorem core_cell_range (h : Heap) (fresh : Fresh h) (source dest p : BPtr) (capacity v : UInt64)
    (good : LocalGood (coreHeap h source dest capacity) h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)) (cell : LengthCell h p v) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) p 8 true :=
  core_old_range h fresh source dest p capacity 8 (lengthBytes v) true good cell.1 (fun _ => cell.2)


#print axioms core_old_range
#print axioms core_reserved_range
#print axioms core_output_range
#print axioms core_remaining_buffers
#print axioms core_cell_range
end Zlib.Uncompr.Proof.LocalWrapperRanges
