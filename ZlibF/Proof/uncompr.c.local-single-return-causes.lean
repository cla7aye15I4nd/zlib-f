import ZlibF.Proof.«uncompr.c.local-wrapper-return-causes»
import ZlibF.Proof.«uncompr.c.local-single-length»

namespace Zlib.Uncompr.Proof.LocalReturnCauses
open C Zlib.Gzguts Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.LocalCallerCells
open Zlib.Uncompr.Proof.ReturnCauses Zlib.Uncompr.Proof.LocalSingleLength
set_option autoImplicit false

/-- The actual single-length z_size_t entry feeds its allocated input cell
to the actual counted wrapper, then frees that same returned cell. All
return causes survive the actual outer cleanup on the same final heap. -/
theorem uncompress_z_return_causes (h after : Heap) (source dest destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (run : C.run (uncompress_z dest destLen source n) h = .ok (rc, after)) :
    UncompressCode rc ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
    (rc = Z_BUF_ERROR → LengthCell after destLen capacity) := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨innerRc, inner, consumed, got, innerRun, tempAfter, outputAfter, _, _, _, _typed, _freshAfter, _fitAfter, kept⟩ :=
    uncompress2_z_caller_cells (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨allowed, memory, buffer⟩ := uncompress2_z_return_causes (scalarHeap h n) inner source dest
    (.ref (.blk h.nextBlk) 0) destLen n capacity xs innerRc (scalar_fresh h n fresh)
    globals (scalar_platform h n platform)
    (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
    (scalar_old_bytes h n fresh source n.toNat xs readable)
    (scalar_old_writable h n fresh dest capacity.toNat writable)
    separate tempDest cellSeparate tempCell validInput validOutput innerRun
  have unique := kept h.nextBlk (scalar_uniqueFrom h h.nextBlk n (fresh_uniqueFrom h fresh) fresh)
  obtain ⟨freeRun, _⟩ := free_scalar_local inner h.nextBlk consumed h.nextBlk unique (Nat.le_refl _) tempAfter
  have actual : C.run (uncompress_z dest destLen source n) h = .ok (innerRc, freedHeap inner h.nextBlk) := by
    simp only [C.run] at innerRun
    simp [C.run, uncompress_z, scalar_allocate h fresh, scalar_write h n, innerRun, freeRun]
  have same := Except.ok.inj (actual.symm.trans run)
  have code : innerRc = rc := congrArg Prod.fst same
  have heaps : freedHeap inner h.nextBlk = after := congrArg Prod.snd same
  refine ⟨by rw [←code]; exact allowed, ?_, ?_⟩
  · intro selected
    obtain ⟨i, lower, upper, failed⟩ := memory (code.trans selected)
    refine ⟨i, lower, ?_, failed⟩
    rw [←heaps]
    exact upper
  · intro selected
    have cell := freed_cell inner h.nextBlk destLen capacity (buffer (code.trans selected))
      (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
    rw [heaps] at cell
    exact cell

#print axioms uncompress_z_return_causes
end Zlib.Uncompr.Proof.LocalReturnCauses
