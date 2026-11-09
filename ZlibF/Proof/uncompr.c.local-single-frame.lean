import ZlibF.Proof.«uncompr.c.local-single-length»
import ZlibF.Proof.«uncompr.c.local-wrapper-frame»
import ZlibF.Proof.«uncompr.c.single-frame»

namespace Zlib.Uncompr.Proof.LocalSingleLength
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
set_option autoImplicit false

/-- The ordinary object frame of the same actual single-length call. Its
temporary scalar root is hidden using its real allocation age, not a public
uniqueness premise. Exact byte Stores remain a separate target. -/
theorem uncompress_z_frame_of_run (h : Heap) (source dest destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (rc : Int32) (after : Heap)
    (actual : C.run (uncompress_z dest destLen source n) h = .ok (rc, after)) :
    Frame h after (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨calleeRc, inner, consumed, got, run, tempAfter, _outputAfter, _inputBound, _gotBound,
    _live, _typed, _freshAfter, _fitAfter, kept⟩ :=
    LocalCallerCells.uncompress2_z_caller_cells (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨otherRc, otherHeap, otherRun, _, _, _, frame⟩ :=
    LocalWrapperFrame.uncompress2_z_framed_memory (scalarHeap h n) source dest
      (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  cases Except.ok.inj (otherRun.symm.trans run)
  have unique := kept h.nextBlk (scalar_uniqueFrom h h.nextBlk n (fresh_uniqueFrom h fresh) fresh)
  obtain ⟨freeRun, _freeLedger⟩ := free_scalar_local inner h.nextBlk consumed h.nextBlk unique (Nat.le_refl _) tempAfter
  have complete : C.run (uncompress_z dest destLen source n) h =
      .ok (calleeRc, freedHeap inner h.nextBlk) := by
    simp only [C.run] at run
    simp [C.run, uncompress_z, scalar_allocate h fresh, scalar_write h n, run, freeRun]
  cases Except.ok.inj (complete.symm.trans actual)
  have beforeFree : Frame h inner (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
    apply CallerFrame.frame_trans_restrict (OuterFrame.scalar_prefix_frame h n fresh) frame
    intro b alive outside
    refine ⟨by simp, ?_⟩
    have below := fresh.lt alive
    rintro (destRoot | temporary | lengthRoot)
    · exact outside (Or.inl destRoot)
    · change b = h.nextBlk at temporary
      omega
    · exact outside (Or.inr lengthRoot)
  apply CallerFrame.frame_trans_restrict beforeFree (OuterFrame.local_free_frame inner h.nextBlk)
  intro b alive outside
  have below := fresh.lt alive
  exact ⟨outside, by change b ≠ h.nextBlk; omega⟩

/-- Memory, exact live accounting and the ordinary object frame concern the
same actual whole call, including all initialization allocation outcomes. -/
theorem uncompress_z_framed_memory (h : Heap) (source dest destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
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
      Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧ UniqueFrom after h.nextBlk ∧
      Frame h after (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
  obtain ⟨rc, after, got, run, cell, bound, live, freshAfter, fitAfter, unique⟩ :=
    uncompress_z_memory h source dest destLen n capacity xs fresh globals platform outputCell
      readable writable separate cellSeparate validInput validOutput
  exact ⟨rc, after, got, run, cell, bound, live, freshAfter, fitAfter, unique,
    uncompress_z_frame_of_run h source dest destLen n capacity xs fresh globals platform outputCell
      readable writable separate cellSeparate validInput validOutput rc after run⟩

#print axioms uncompress_z_frame_of_run
#print axioms uncompress_z_framed_memory
end Zlib.Uncompr.Proof.LocalSingleLength
