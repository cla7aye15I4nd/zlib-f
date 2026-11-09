import ZlibF.Proof.«uncompr.c.store-frame»

/-!
# Actual single-length wrapper output stores and caller frame

The real outer scalar prefix frames the original caller. The counted callee's
exact output Store is mirrored, its fresh private scalar Store is hidden, and
its external scalar Store is mirrored. Its real returning Frame then composes
with the actual outer free. Output intervals remain exact, including shared byte
allocations. All allocation outcomes retain exact final observations or the
initial-memory-failure capacity fallback. SameObjects and format remain open.
-/

set_option autoImplicit false

namespace Zlib.Uncompr.Proof.OuterFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.CallerFrame

theorem scalar_prefix_frame (h : Heap) (n : UInt64) (fresh : Fresh h) :
    Frame h (scalarHeap h n) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, by change h.nextBlk ≤ h.nextBlk + 1; omega, Nat.le_refl _, ?_⟩
  intro b live _
  have below := fresh.lt live
  simp [scalarHeap, show b ≠ h.nextBlk by omega]

theorem local_store_frame {h after : Heap} {block : Nat} {xs : List UInt8}
    (store : Store h (.ref (.blk block) 0) xs after) : Frame h after (fun b => b = block) := by
  rcases store with ⟨_, same⟩ | ⟨ref, off, array, pointer, _get, _write, _room, same⟩
  · rw [same]
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => by simp⟩
  · cases pointer
    rw [same]
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ outside
    simp [Space.put, outside]

theorem local_free_frame (h : Heap) (block : Nat) : Frame h (freedHeap h block) (fun b => b = block) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ outside
  simp [freedHeap, outside]

theorem hide_local_store {h expected actual written : Heap} {block : Nat} {xs : List UInt8}
    (fresh : Fresh h) (shape : Shape h expected) (new : h.nextBlk ≤ block)
    (frame : Frame expected actual (fun _ => False))
    (store : Store actual (.ref (.blk block) 0) xs written) : Frame expected written (fun _ => False) := by
  apply frame_trans_restrict frame (local_store_frame store)
  intro b live _
  have below := fresh.lt ((shape.live b).mp live)
  exact ⟨by simp, by omega⟩

theorem hide_local_free {h expected actual : Heap} {block : Nat}
    (fresh : Fresh h) (shape : Shape h expected) (new : h.nextBlk ≤ block)
    (frame : Frame expected actual (fun _ => False)) : Frame expected (freedHeap actual block) (fun _ => False) := by
  apply frame_trans_restrict frame (local_free_frame actual block)
  intro b live _
  have below := fresh.lt ((shape.live b).mp live)
  exact ⟨by simp, by omega⟩

theorem freed_bytes (h : Heap) (block : Nat) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (outside : ∀ off, p ≠ .ref (.blk block) off) :
    Bytes (freedHeap h block) p count xs := by
  rcases bytes with null | ⟨ref, off, array, ptr, get, room, values⟩
  · exact Or.inl null
  · refine Or.inr ⟨ref, off, array, ptr, ?_, room, values⟩
    cases ref with
    | blk b =>
      have different : b ≠ block := by intro same; subst b; exact outside off ptr
      simpa [Space.get, freedHeap, different] using get
    | dstate_depth b => exact get
    | str i => exact get
    | st_dist_code => exact get
    | st_length_code => exact get

theorem bytes_root_live (h : Heap) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (b : Nat) (root : ByteRoot p b) : h.live b := by
  rcases bytes with null | ⟨ref, off, array, ptr, get, _⟩
  · rw [null.1] at root
    cases root
  · subst p
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      exact Or.inl (by simp [show h.bytes i = some array from get])
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some s => simp [Heap.live, state]
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root


theorem uncompress_z_framed_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellOutput : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after output used got first expected,
      C.run (uncompress_z dest destLen source n) h = .ok (rc, after) ∧
      Store h dest output first ∧ Store first destLen (lengthBytes got) expected ∧ Frame expected after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ Bytes after dest output.length output ∧
      LengthCell after destLen got ∧ used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      (got.toNat = output.length ∨ (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity)) := by
  obtain ⟨oldOutput, oldReadable⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempOutput := scalar_separate_old h fresh dest capacity.toNat oldOutput oldReadable
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, inner, output, used, got, consumed, calleeFirst, calleeSecond, calleeExpected,
    run, outputStore, localStore, destStore, calleeFrame, live, observed, localCell, outputAfter,
    usedBound, madeBound, counts⟩ :=
    Zlib.Uncompr.Proof.WrapperStoreFrame.uncompress2_z_framed_memory (scalarHeap h n) source dest
      (.ref (.blk h.nextBlk) 0) destLen n capacity xs (scalar_fresh h n fresh) (scalar_uniq h n uniq fresh)
      globals (scalar_platform h n platform) (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable) (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempOutput cellOutput tempCell validInput validOutput
  have shape := Zlib.Uncompr.Proof.WrapperShape.uncompress2_z_return_shape (scalarHeap h n) inner source dest
    (.ref (.blk h.nextBlk) 0) destLen n capacity xs rc (scalar_fresh h n fresh) (scalar_uniq h n uniq fresh)
    globals (scalar_platform h n platform) (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
    (scalar_old_bytes h n fresh source n.toNat xs readable) (scalar_old_writable h n fresh dest capacity.toNat writable)
    separate tempOutput cellOutput tempCell validInput validOutput run
  obtain ⟨freeRun, freeLedger⟩ := free_scalar inner h.nextBlk consumed shape.1 localCell
  have finalOutput := freed_bytes inner h.nextBlk dest output.length output observed
    (old_not_scalar h fresh dest capacity.toNat oldOutput oldReadable)
  have finalCell := freed_cell inner h.nextBlk destLen got outputAfter
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)

  have outputRoots : ∀ b, ByteRoot dest b → h.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨bytes_root_live h dest capacity.toNat oldOutput oldReadable b root, by simp⟩
  obtain ⟨first, expectedOutputStore, dataFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror (scalar_prefix_frame h n fresh) outputRoots outputStore
  have localFrame := hide_local_store fresh expectedOutputStore.shape (Nat.le_refl _) dataFrame localStore
  have destRoots : ∀ b, ByteRoot destLen b → first.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨(expectedOutputStore.shape.live b).mpr (bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 b root), by simp⟩
  obtain ⟨expected, expectedDestStore, expectedFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror localFrame destRoots destStore
  have beforeFree : Frame expected inner (fun _ => False) :=
    frame_trans_restrict expectedFrame calleeFrame (fun _ _ _ => ⟨by simp, by simp⟩)
  have finalFrame := hide_local_free fresh (expectedOutputStore.shape.trans expectedDestStore.shape) (Nat.le_refl _) beforeFree
  have counted : got.toNat = output.length ∨ (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity) := by
    rcases counts with ⟨correct, _⟩ | ⟨memory, empty, capacityEq, _⟩
    · exact Or.inl correct
    · exact Or.inr ⟨memory, empty, capacityEq⟩
  refine ⟨rc, freedHeap inner h.nextBlk, output, used, got, first, expected, ?_,
    expectedOutputStore, expectedDestStore, finalFrame, ?_, finalOutput, finalCell, usedBound, madeBound, counted⟩
  · simp only [C.run] at run
    simp [C.run, uncompress_z, scalar_allocate h fresh, scalar_write h n, run, freeRun]
  · intro x
    have middle : inner.live x ↔ (scalarHeap h n).live x := by
      simpa only [not_false_eq_true, and_true, or_false] using live x
    have outer := freeLedger x
    have initial := scalar_live h n x
    constructor
    · intro current
      obtain ⟨old, outside⟩ := (outer.mp current).resolve_right (by simp)
      rcases initial.mp (middle.mp old) with original | temporary
      · exact Or.inl ⟨original, by simp⟩
      · exact False.elim (outside temporary)
    · rintro (⟨original, _⟩ | impossible)
      · have different : x ≠ h.nextBlk := by have below := fresh.lt original; omega
        exact outer.mpr (Or.inl ⟨middle.mpr (initial.mpr (Or.inl original)), different⟩)
      · exact False.elim impossible

#print axioms uncompress_z_framed_memory

#print axioms hide_local_store
end Zlib.Uncompr.Proof.OuterFrame
