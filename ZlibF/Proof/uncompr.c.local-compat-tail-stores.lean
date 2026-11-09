import ZlibF.Proof.«uncompr.c.local-compat-tail»
import ZlibF.Proof.«uncompr.c.local-buffer-coarse-frame»

/-! Ordinary root frame of the original ordered compatibility tail. -/
namespace Zlib.Uncompr.Proof.LocalCompatibilityStores
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.CompatibilityTail
set_option autoImplicit false

theorem free_frame (h : Heap) (block : Nat) :
    Frame h (freedHeap h block) (fun x => x = block) := by
  refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
  intro x live outside
  simp [freedHeap,outside]

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases p <;> cases q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

private theorem outside_separate (p : BPtr) (count block : Nat)
    (outside : ∀ off, p ≠ .ref (.blk block) off) :
    Separate p count (.ref (.blk block) 0) 8 := by
  cases p with
  | null => simp [Separate]
  | ref ref off =>
    have different : ref ≠ .blk block := by intro same; subst ref; exact outside off rfl
    exact Or.inr (Or.inr (Or.inl different))

theorem finish_stores (h : Heap) (cutoff gotBlock usedBlock : Nat) (destLen sourceLen : BPtr)
    (sourceOld destOld gotValue usedValue : UInt64) (rc : Int32)
    (uniq : UniqueFrom h cutoff) (fresh : Fresh h)
    (gotAge : cutoff ≤ gotBlock) (usedAge : cutoff ≤ usedBlock) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (sourceCell : LengthCell h sourceLen sourceOld) (destCell : LengthCell h destLen destOld)
    (gotCell : LengthCell h (.ref (.blk gotBlock) 0) gotValue)
    (usedCell : LengthCell h (.ref (.blk usedBlock) 0) usedValue)
    (distinct : gotBlock ≠ usedBlock) (separate : Separate sourceLen 8 destLen 8)
    (sourceGot : ∀ off, sourceLen ≠ .ref (.blk gotBlock) off)
    (sourceUsed : ∀ off, sourceLen ≠ .ref (.blk usedBlock) off)
    (destGot : ∀ off, destLen ≠ .ref (.blk gotBlock) off)
    (destUsed : ∀ off, destLen ≠ .ref (.blk usedBlock) off) :
    ∃ first second after,
      C.run (finish destLen sourceLen (.ref (.blk gotBlock) 0) (.ref (.blk usedBlock) 0) rc) h = .ok (rc, after) ∧
      Store h sourceLen (lengthBytes usedValue) first ∧ Store first destLen (lengthBytes gotValue) second ∧
      Frame second after (fun x => x = gotBlock ∨ x = usedBlock) := by
  have srcGot := outside_separate sourceLen 8 gotBlock sourceGot
  have srcUsed := outside_separate sourceLen 8 usedBlock sourceUsed
  have dstGot := outside_separate destLen 8 gotBlock destGot
  have dstUsed := outside_separate destLen 8 usedBlock destUsed
  obtain ⟨first, sourceRun, sourceStore, writtenSource, sourceLive, shape1, fresh1, fit1, keep1⟩ :=
    LocalScalarWriteback.writable_scalar_store h sourceLen usedValue sourceCell.2 fresh platform
  have unique1 := LocalWrapperShape.Shape.uniqueFrom shape1 cutoff uniq
  have got1 := keep1 (.ref (.blk gotBlock) 0) gotValue gotCell (separate_symm _ _ _ _ srcGot)
  have used1 := keep1 (.ref (.blk usedBlock) 0) usedValue usedCell (separate_symm _ _ _ _ srcUsed)
  have dest1 := keep1 destLen destOld destCell (separate_symm _ _ _ _ separate)
  obtain ⟨second, destRun, destStore, writtenDest, destLive, shape2, fresh2, fit2, keep2⟩ :=
    LocalScalarWriteback.writable_scalar_store first destLen gotValue dest1.2 fresh1 fit1
  have unique2 := LocalWrapperShape.Shape.uniqueFrom shape2 cutoff unique1
  have source2 := keep2 sourceLen usedValue writtenSource separate
  have got2 := keep2 (.ref (.blk gotBlock) 0) gotValue got1 (separate_symm _ _ _ _ dstGot)
  have used2 := keep2 (.ref (.blk usedBlock) 0) usedValue used1 (separate_symm _ _ _ _ dstUsed)
  obtain ⟨freeGot, gotLive⟩ := LocalSingleLength.free_scalar_local second gotBlock gotValue cutoff unique2 gotAge got2
  have unique3 := LocalSingleLength.freed_uniqueFrom second cutoff gotBlock unique2
  have used3 := freed_cell second gotBlock (.ref (.blk usedBlock) 0) usedValue used2 (by
    intro off same
    have blocks : usedBlock = gotBlock := BRef.blk.inj (Ptr.ref.inj same).1
    exact distinct blocks.symm)
  obtain ⟨freeUsed, usedLive⟩ := LocalSingleLength.free_scalar_local (freedHeap second gotBlock) usedBlock usedValue cutoff unique3 usedAge used3
  let final := freedHeap (freedHeap second gotBlock) usedBlock
  refine ⟨first,second,final,?_,sourceStore,destStore,?_⟩
  · have readUsed := load64_lengthCell h (.ref (.blk usedBlock) 0) usedValue usedCell
    have readGot := load64_lengthCell first (.ref (.blk gotBlock) 0) gotValue got1
    simp only [C.run] at sourceRun destRun readUsed readGot
    simp [C.run,finish,readUsed,sourceRun,readGot,destRun,freeGot,freeUsed,final]
  · apply CallerFrame.frame_trans_restrict (free_frame second gotBlock)
      (free_frame (freedHeap second gotBlock) usedBlock)
    intro x live outside
    exact ⟨fun root => outside (Or.inl root), fun root => outside (Or.inr root)⟩

#print axioms finish_stores
end Zlib.Uncompr.Proof.LocalCompatibilityStores
