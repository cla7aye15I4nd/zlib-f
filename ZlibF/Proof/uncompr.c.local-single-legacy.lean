import ZlibF.Proof.«uncompr.c.local-legacy-cutoff»

/-! Actual traditional single-length wrapper: its own earlier scalar, the
real two-scalar compatibility callee and the same returned scalar free. -/
namespace Zlib.Uncompr.Proof.LocalLegacySingle
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
set_option autoImplicit false

/-- `int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`
+
+All allocation outcomes and final releases follow the actual call chain.
+Earlier local uniqueness is derived from Fresh; the caller has no global
+uniqueness obligation. Format correctness remains a separate target. -/
theorem uncompress_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
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
      UniqueFrom after h.nextBlk ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, got, run, tempAfter, outputAfter, _inputBound, gotBound, live, unique, freshAfter, fitAfter⟩ :=
    LocalLegacyCutoff.uncompress2_memory_at_cutoff (scalarHeap h n) h.nextBlk source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh)
      (LocalSingleLength.scalar_uniqueFrom h h.nextBlk n (LocalSingleLength.fresh_uniqueFrom h fresh) fresh)
      (by change h.nextBlk ≤ h.nextBlk + 1; omega) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨freeRun, freeLedger⟩ := LocalSingleLength.free_scalar_local after h.nextBlk consumed h.nextBlk unique (Nat.le_refl _) tempAfter
  have finalCell := freed_cell after h.nextBlk destLen got outputAfter
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  refine ⟨rc, freedHeap after h.nextBlk, got, ?_, finalCell, gotBound, ?_,
    LocalSingleLength.freed_uniqueFrom after h.nextBlk h.nextBlk unique, freed_fresh after h.nextBlk freshAfter,
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
end Zlib.Uncompr.Proof.LocalLegacySingle
