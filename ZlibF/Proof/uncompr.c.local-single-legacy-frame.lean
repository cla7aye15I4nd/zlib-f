import ZlibF.Proof.«uncompr.c.local-single-legacy»
import ZlibF.Proof.«uncompr.c.local-legacy-frame»

namespace Zlib.Uncompr.Proof.LocalLegacySingle
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
set_option autoImplicit false

private theorem scalar_prefix_frame (h : Heap) (n : UInt64) (fresh : Fresh h) :
    Frame h (scalarHeap h n) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, by change h.nextBlk ≤ h.nextBlk + 1; omega, Nat.le_refl _, ?_⟩
  intro b live _
  have below := fresh.lt live
  simp [scalarHeap, show b ≠ h.nextBlk by omega]

private theorem local_free_frame (h : Heap) (block : Nat) :
    Frame h (freedHeap h block) (fun b => b = block) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ outside
  simp [freedHeap, outside]

theorem uncompress_frame_of_run (h : Heap) (source dest destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (rc : Int32) (after : Heap)
    (actual : C.run (uncompress dest destLen source n) h = .ok (rc, after)) :
    Frame h after (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨calleeRc, inner, consumed, got, run, tempAfter, outputAfter, _inputBound, gotBound, live, unique, freshAfter, fitAfter⟩ :=
    LocalLegacyCutoff.uncompress2_memory_at_cutoff (scalarHeap h n) h.nextBlk source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh)
      (LocalSingleLength.scalar_uniqueFrom h h.nextBlk n (LocalSingleLength.fresh_uniqueFrom h fresh) fresh)
      (by change h.nextBlk ≤ h.nextBlk + 1; omega) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨otherRc,otherHeap,otherRun,frame⟩ :=
    LocalLegacyFrame.uncompress2_frame (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  cases Except.ok.inj (otherRun.symm.trans run)
  obtain ⟨freeRun, freeLedger⟩ := LocalSingleLength.free_scalar_local inner h.nextBlk consumed h.nextBlk unique (Nat.le_refl _) tempAfter
  have complete : C.run (uncompress dest destLen source n) h =
      .ok (calleeRc, freedHeap inner h.nextBlk) := by
    simp only [C.run] at run
    simp [C.run, uncompress, scalar_allocate h fresh, scalar_write h n, run, freeRun]
  cases Except.ok.inj (complete.symm.trans actual)
  have beforeFree : Frame h inner (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
    apply CallerFrame.frame_trans_restrict (scalar_prefix_frame h n fresh) frame
    intro b alive outside
    refine ⟨by simp, ?_⟩
    have below := fresh.lt alive
    rintro (destRoot | temporary | lengthRoot)
    · exact outside (Or.inl destRoot)
    · change b = h.nextBlk at temporary
      omega
    · exact outside (Or.inr lengthRoot)
  apply CallerFrame.frame_trans_restrict beforeFree (local_free_frame inner h.nextBlk)
  intro b alive outside
  have below := fresh.lt alive
  exact ⟨outside, by change b ≠ h.nextBlk; omega⟩

theorem uncompress_framed_memory (h : Heap) (source dest destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
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
      Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧ UniqueFrom after h.nextBlk ∧
      Frame h after (fun b => ByteRoot dest b ∨ ByteRoot destLen b) := by
  obtain ⟨rc, after, got, run, cell, bound, live, unique, freshAfter, fitAfter⟩ :=
    uncompress_memory h source dest destLen n capacity xs fresh globals platform outputCell
      readable writable separate cellSeparate validInput validOutput
  exact ⟨rc, after, got, run, cell, bound, live, freshAfter, fitAfter, unique,
    uncompress_frame_of_run h source dest destLen n capacity xs fresh globals platform outputCell
      readable writable separate cellSeparate validInput validOutput rc after run⟩


#print axioms uncompress_frame_of_run
#print axioms uncompress_framed_memory
end Zlib.Uncompr.Proof.LocalLegacySingle
