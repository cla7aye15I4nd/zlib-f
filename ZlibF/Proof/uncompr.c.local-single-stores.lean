import ZlibF.Proof.«uncompr.c.local-store-observations»
import ZlibF.Proof.«uncompr.c.local-single-length»
import ZlibF.Proof.«uncompr.c.single-frame»

namespace Zlib.Uncompr.Proof.LocalSingleStores
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.OuterFrame
open Zlib.Uncompr.Proof.LocalSingleLength Zlib.Uncompr.Proof.CallerFrame
set_option autoImplicit false

/-- Actual z_size_t single-length utility: the private input-cell Store is
hidden, the output and external length Stores are mirrored, and the same
returned private object is actually freed. No global caller uniqueness. -/
theorem uncompress_z_stores (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64)
    (xs : List UInt8) (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after output produced first expected,
      C.run (uncompress_z dest destLen source n) h = .ok (rc,after) ∧
      Store h dest output first ∧ Store first destLen (lengthBytes produced) expected ∧
      Frame expected after (fun _ => False) ∧ LengthCell after destLen produced ∧
      (output.length = produced.toNat ∨ (rc = Z_MEM_ERROR ∧ output = [] ∧ produced = capacity)) := by
  obtain ⟨oldOutput,oldReadable⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempOutput := scalar_separate_old h fresh dest capacity.toNat oldOutput oldReadable
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc,inner,used,got,run,tempAfter,outputAfter,_inputBound,_outputBound,
      _live,_shape,_fresh,_fit,kept⟩ :=
    LocalCallerCells.uncompress2_z_caller_cells (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempOutput cellSeparate tempCell validInput validOutput
  obtain ⟨output,consumed,produced,calleeFirst,calleeSecond,calleeExpected,outputStore,
      localStore,destStore,calleeFrame,counts⟩ :=
    LocalWrapperStores.uncompress2_z_stores_allocation (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen
      n capacity xs (scalar_fresh h n fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempOutput cellSeparate tempCell validInput validOutput rc inner run
  have cells := LocalStoreObservations.counted_cells localStore destStore calleeFrame tempCell
  have unique := kept h.nextBlk (scalar_uniqueFrom h h.nextBlk n (fresh_uniqueFrom h fresh) fresh)
  obtain ⟨freeRun,_⟩ := free_scalar_local inner h.nextBlk used h.nextBlk unique (Nat.le_refl _) tempAfter
  have finalCell := freed_cell inner h.nextBlk destLen produced cells.2
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  have outputRoots : ∀ b,ByteRoot dest b → h.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨bytes_root_live h dest capacity.toNat oldOutput oldReadable b root,by simp⟩
  obtain ⟨first,expectedOutputStore,dataFrame⟩ := FrameMirror.store_mirror
    (scalar_prefix_frame h n fresh) outputRoots outputStore
  have localFrame := hide_local_store fresh expectedOutputStore.shape (Nat.le_refl _) dataFrame localStore
  have destRoots : ∀ b,ByteRoot destLen b → first.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨(expectedOutputStore.shape.live b).mpr (bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 b root),by simp⟩
  obtain ⟨expected,expectedDestStore,expectedFrame⟩ := FrameMirror.store_mirror localFrame destRoots destStore
  have beforeFree : Frame expected inner (fun _ => False) :=
    frame_trans_restrict expectedFrame calleeFrame (fun _ _ _ => ⟨by simp,by simp⟩)
  have finalFrame := hide_local_free fresh (expectedOutputStore.shape.trans expectedDestStore.shape) (Nat.le_refl _) beforeFree
  refine ⟨rc,freedHeap inner h.nextBlk,output,produced,first,expected,?_,
    expectedOutputStore,expectedDestStore,finalFrame,finalCell,?_⟩
  · simp only [C.run] at run
    simp [C.run,uncompress_z,scalar_allocate h fresh,scalar_write h n,run,freeRun]
  · rcases counts with ⟨length,_,_⟩ | ⟨memory,empty,_used,producedEq⟩
    · exact Or.inl length
    · exact Or.inr ⟨memory,empty,producedEq⟩

#print axioms uncompress_z_stores
end Zlib.Uncompr.Proof.LocalSingleStores
