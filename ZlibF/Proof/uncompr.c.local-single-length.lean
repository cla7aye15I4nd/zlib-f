import ZlibF.Proof.«uncompr.c.local-caller-cells»
import ZlibF.Proof.«uncompr.c.local-scalar-support»

/-! The actual single-length utility with arbitrary older caller allocation
types. Only the scalar created by this entry needs a local uniqueness fact. -/
namespace Zlib.Uncompr.Proof.LocalSingleLength
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
set_option autoImplicit false

/-- `int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`

The real scalar allocation and write precede the actual counted call. Typed
shape transports uniqueness at this earlier allocation cutoff to the same
returned heap, where the scalar is actually freed. All allocation outcomes
are included. Independent format and the full public Goal remain open. -/
theorem uncompress_z_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after got,
      C.run (uncompress_z dest destLen source n) h = .ok (rc, after) ∧
      LengthCell after destLen got ∧ got.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧ UniqueFrom after h.nextBlk := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, got, run, tempAfter, outputAfter, _inputBound, gotBound,
    live, _typed, freshAfter, fitAfter, kept⟩ :=
    LocalCallerCells.uncompress2_z_caller_cells (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  have unique := kept h.nextBlk (scalar_uniqueFrom h h.nextBlk n (fresh_uniqueFrom h fresh) fresh)
  obtain ⟨freeRun, freeLedger⟩ := free_scalar_local after h.nextBlk consumed h.nextBlk unique (Nat.le_refl _) tempAfter
  have finalCell := freed_cell after h.nextBlk destLen got outputAfter
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  refine ⟨rc, freedHeap after h.nextBlk, got, ?_, finalCell, gotBound, ?_,
    freed_fresh after h.nextBlk freshAfter,
    Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform after h.nextBlk fitAfter,
    freed_uniqueFrom after h.nextBlk h.nextBlk unique⟩
  · simp only [C.run] at run
    simp [C.run, uncompress_z, scalar_allocate h fresh, scalar_write h n, run, freeRun]
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

#print axioms uncompress_z_memory
end Zlib.Uncompr.Proof.LocalSingleLength
