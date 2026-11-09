import ZlibF.Proof.«uncompr.c.legacy-frame»

/-!
# Actual traditional single-length stores and complete caller frame

The traditional counted wrapper runs on the real outer scalar heap. Exact
output and external length Stores are mirrored to the original caller, while
its fresh private scalar Store and final free remain private. The same actual
execution returns final Bytes, a complete caller Frame, no allocation residue
and the correct capacity/count fallback for every allocation outcome. The
public SameObjects and independent format/END targets remain separate.
-/

set_option autoImplicit false

namespace Zlib.Uncompr.Proof.LegacyOuterFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.OuterFrame Zlib.Uncompr.Proof.CallerFrame

theorem uncompress_framed_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellOutput : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after output used got first expected,
      C.run (uncompress dest destLen source n) h = .ok (rc, after) ∧
      Store h dest output first ∧ Store first destLen (lengthBytes got) expected ∧ Frame expected after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ Bytes after dest output.length output ∧
      LengthCell after destLen got ∧ used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      (got.toNat = output.length ∨ (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity)) := by
  obtain ⟨oldOutput, oldReadable⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempOutput := scalar_separate_old h fresh dest capacity.toNat oldOutput oldReadable
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, inner, output, used, got, consumed, calleeFirst, calleeSecond, calleeExpected,
    run, outputStore, localStore, destStore, calleeFrame, live, observed, localCell, outputAfter,
    usedBound, madeBound, counts, innerUnique, _innerFresh, _innerFit⟩ :=
    Zlib.Uncompr.Proof.LegacyFrame.uncompress2_framed_memory (scalarHeap h n) source dest
      (.ref (.blk h.nextBlk) 0) destLen n capacity xs (scalar_fresh h n fresh) (scalar_uniq h n uniq fresh)
      globals (scalar_platform h n platform) (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable) (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempOutput cellOutput tempCell validInput validOutput
  obtain ⟨freeRun, freeLedger⟩ := free_scalar inner h.nextBlk consumed innerUnique localCell
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
    simp [C.run, uncompress, scalar_allocate h fresh, scalar_write h n, run, freeRun]
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

#print axioms uncompress_framed_memory
end Zlib.Uncompr.Proof.LegacyOuterFrame
