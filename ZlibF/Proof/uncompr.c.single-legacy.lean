import ZlibF.Proof.«uncompr.c.legacy-memory»

/-!
# Actual traditional single-length wrapper memory safety

The real temporary scalar feeds the proved actual traditional counted wrapper.
The same returning heap supports its final automatic free. All allocator outcomes
preserve the external length cell, bounded returned value, no allocation residue
and heap shape. Independent format correctness and the public full frame remain
separate obligations.
-/

namespace Zlib.Uncompr.Proof.LegacySingle
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength

/-- The actual traditional single-length entry uses a real automatic scalar,
then the actual traditional counted wrapper and the same returned scalar free.
All allocator outcomes are included; no callee contract is assumed. -/
theorem uncompress_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after got,
      C.run (uncompress dest destLen source n) h = .ok (rc, after) ∧
      LengthCell after destLen got ∧ got.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, got, run, tempAfter, outputAfter, _inputBound, gotBound, live, unique, freshAfter, fitAfter⟩ :=
    Zlib.Uncompr.Proof.LegacyMemory.uncompress2_memory (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) (scalar_uniq h n uniq fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨freeRun, freeLedger⟩ := free_scalar after h.nextBlk consumed unique tempAfter
  have finalCell := freed_cell after h.nextBlk destLen got outputAfter
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  refine ⟨rc, freedHeap after h.nextBlk, got, ?_, finalCell, gotBound, ?_,
    freed_uniq after h.nextBlk unique, freed_fresh after h.nextBlk freshAfter,
    Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform after h.nextBlk fitAfter⟩
  · simp only [C.run] at run
    simp [C.run, uncompress, scalar_allocate h fresh, scalar_write h n, run, freeRun]
  · intro x
    have inner : after.live x ↔ (scalarHeap h n).live x := by
      simpa only [not_false_eq_true, and_true, or_false] using live x
    have outer := freeLedger x
    have beginning := scalar_live h n x
    constructor
    · intro current
      obtain ⟨old, outside⟩ := (outer.mp current).resolve_right (by simp)
      rcases beginning.mp (inner.mp old) with original | temporary
      · exact Or.inl ⟨original, by simp⟩
      · exact False.elim (outside temporary)
    · rintro (⟨original, _⟩ | impossible)
      · have different : x ≠ h.nextBlk := by have below := fresh.lt original; omega
        exact outer.mpr (Or.inl ⟨inner.mpr (beginning.mpr (Or.inl original)), different⟩)
      · exact False.elim impossible

#print axioms uncompress_memory
end Zlib.Uncompr.Proof.LegacySingle
