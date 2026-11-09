import ZlibF.Proof.«uncompr.c.local-legacy-memory»
import ZlibF.Proof.«uncompr.c.local-compat-continuation-frame»

namespace Zlib.Uncompr.Proof.LocalLegacyFrame
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.LocalCompatPrefix
open Zlib.Uncompr.Proof.CallerObjects
set_option autoImplicit false

theorem prepared_frame (h : Heap) (capacity n : UInt64) (fresh : Fresh h) :
    Frame h (preparedHeap h capacity n) (fun _ => False) := by
  refine ⟨rfl,rfl,rfl,by change h.nextBlk ≤ h.nextBlk+2;omega,Nat.le_refl _,?_⟩
  intro x live outside
  have below := fresh.lt live
  simp [preparedHeap, Zlib.Uncompr.Proof.SingleLength.scalarHeap,
    show x ≠ h.nextBlk by omega,show x ≠ h.nextBlk+1 by omega]

/-- Both original scalar allocations/stores precede the actual counted callee.
Its complete execution and external writes/frees have one ordinary root frame.
No caller-wide uniqueness is required. Exact byte Stores stay separate. -/
private theorem local_separate_old (h : Heap) (fresh : Fresh h) (block : Nat) (new : h.nextBlk ≤ block)
    (p : BPtr) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    Separate (.ref (.blk block) 0) 8 p count := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, _, _⟩
  · simp [Separate, null.1]
  · subst p
    have distinct : (.blk block : BRef) ≠ ref := by
      intro same
      subst ref
      have live : h.live block := Or.inl (by simp [show h.bytes block = some a from get])
      exact fresh block new live
    exact Or.inr (Or.inr (Or.inl distinct))

theorem uncompress2_frame (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after,
      C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc,after) ∧
      Frame h after (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
  let prepared := preparedHeap h capacity n
  have fresh0 := prepared_fresh h capacity n fresh
  have unique0 := prepared_uniqueFrom h capacity n fresh
  have globals0 := prepared_globals h capacity n globals
  have fit0 := prepared_platform h capacity n platform
  have gotCell := prepared_got_cell h capacity n fresh
  have usedCell := prepared_used_cell h capacity n
  have sourceCell0 := prepared_old_cell h capacity n fresh sourceLen n inputCell
  have destCell0 := prepared_old_cell h capacity n fresh destLen capacity outputCell
  have oldBytes := prepared_old_bytes h capacity n fresh
  have oldWritable := prepared_old_writable h capacity n fresh
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc,after,run,calleeFrame⟩ :=
    LocalCompatibilityFrame.continuation_frame prepared h.nextBlk h.nextBlk (h.nextBlk + 1) dest destLen source sourceLen n capacity xs
      fresh0 unique0 globals0 (by omega) (by omega) fit0 sourceCell0 destCell0 gotCell usedCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate gotOutput usedOutput sourceOutput destOutput (by omega) cellSeparate
      sourceGot sourceUsed destGot destUsed validInput validOutput
  refine ⟨rc,after,?_,?_⟩
  · rw [uncompress2_to_continuation h dest destLen source sourceLen capacity n fresh outputCell inputCell]
    exact run
  · apply CallerFrame.frame_trans_restrict (prepared_frame h capacity n fresh) calleeFrame
    intro x live outside
    refine ⟨by simp,?_⟩
    have below := fresh.lt live
    rintro (output | source | dest | got | used)
    · exact outside (Or.inl output)
    · exact outside (Or.inr (Or.inl source))
    · exact outside (Or.inr (Or.inr dest))
    · omega
    · omega

theorem uncompress2_frame_of_run (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) 
    (rc : Int32) (after : Heap)
    (actual : C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc,after)) :
    Frame h after (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
  obtain ⟨otherRc,otherHeap,run,frame⟩ := uncompress2_frame h source dest sourceLen destLen n capacity xs
    fresh globals platform inputCell outputCell readable writable separate sourceOutput destOutput
    cellSeparate validInput validOutput
  cases Except.ok.inj (run.symm.trans actual)
  exact frame

theorem uncompress2_framed_memory (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after consumed produced,
      C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc, after) ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen produced ∧
      consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      UniqueFrom after h.nextBlk ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      Frame h after (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
  obtain ⟨rc,after,consumed,produced,run,sourceCell,destCell,inputBound,outputBound,
    live,unique,afterFresh,fit⟩ :=
    LocalLegacyMemory.uncompress2_memory h source dest sourceLen destLen n capacity xs
      fresh globals platform inputCell outputCell readable writable separate sourceOutput destOutput
      cellSeparate validInput validOutput
  exact ⟨rc,after,consumed,produced,run,sourceCell,destCell,inputBound,outputBound,live,unique,afterFresh,fit,
    uncompress2_frame_of_run h source dest sourceLen destLen n capacity xs fresh globals platform
      inputCell outputCell readable writable separate sourceOutput destOutput cellSeparate validInput validOutput rc after run⟩

#print axioms uncompress2_frame_of_run
#print axioms uncompress2_framed_memory
#print axioms uncompress2_frame
end Zlib.Uncompr.Proof.LocalLegacyFrame
