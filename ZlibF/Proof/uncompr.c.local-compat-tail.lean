import ZlibF.Proof.«uncompr.c.local-scalar-writeback»
import ZlibF.Proof.«uncompr.c.local-scalar-support»
import ZlibF.Proof.«uncompr.c.local-wrapper-shape-tail»
import ZlibF.Proof.«uncompr.c.compat-tail»

/-! The actual traditional counted-wrapper tail. Uniqueness is needed only
for its two private scalar objects; old caller allocations are unrestricted. -/
namespace Zlib.Uncompr.Proof.LocalCompatibilityTail
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.CompatibilityTail
open Zlib.Uncompr.Proof.LocalWrapperShape
set_option autoImplicit false

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

/-- Both real scalar stores precede both real frees. Earlier local uniqueness
is preserved through each actual write and used only at those two frees. -/
theorem finish_safe (h : Heap) (cutoff gotBlock usedBlock : Nat) (destLen sourceLen : BPtr)
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
      LengthCell after sourceLen usedValue ∧ LengthCell after destLen gotValue ∧
      LiveChange h after (fun _ => False) (fun x => x = gotBlock ∨ x = usedBlock) ∧
      UniqueFrom after cutoff ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
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
  have fresh3 := freed_fresh second gotBlock fresh2
  have fit3 := Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform second gotBlock fit2
  have used3 := freed_cell second gotBlock (.ref (.blk usedBlock) 0) usedValue used2 (by
    intro off same
    have blocks : usedBlock = gotBlock := BRef.blk.inj (Ptr.ref.inj same).1
    exact distinct blocks.symm)
  obtain ⟨freeUsed, usedLive⟩ := LocalSingleLength.free_scalar_local (freedHeap second gotBlock) usedBlock usedValue cutoff unique3 usedAge used3
  let final := freedHeap (freedHeap second gotBlock) usedBlock
  have sourceFinal := freed_cell (freedHeap second gotBlock) usedBlock sourceLen usedValue
    (freed_cell second gotBlock sourceLen usedValue source2 sourceGot) sourceUsed
  have destFinal := freed_cell (freedHeap second gotBlock) usedBlock destLen gotValue
    (freed_cell second gotBlock destLen gotValue writtenDest destGot) destUsed
  refine ⟨first, second, final, ?_, sourceStore, destStore, sourceFinal, destFinal, ?_,
    LocalSingleLength.freed_uniqueFrom _ cutoff usedBlock unique3, freed_fresh _ usedBlock fresh3,
    Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform _ usedBlock fit3⟩
  · have readUsed := load64_lengthCell h (.ref (.blk usedBlock) 0) usedValue usedCell
    have readGot := load64_lengthCell first (.ref (.blk gotBlock) 0) gotValue got1
    simp only [C.run] at sourceRun destRun readUsed readGot
    simp [C.run, finish, readUsed, sourceRun, readGot, destRun, freeGot, freeUsed, final]
  · intro x
    have firstEq : first.live x ↔ h.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using sourceLive x
    have secondEq : second.live x ↔ first.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using destLive x
    have gotEq : (freedHeap second gotBlock).live x ↔ second.live x ∧ x ≠ gotBlock := by
      simpa only [or_false] using gotLive x
    have usedEq : final.live x ↔ (freedHeap second gotBlock).live x ∧ x ≠ usedBlock := by
      simpa only [or_false] using usedLive x
    change final.live x ↔ (h.live x ∧ ¬ (x = gotBlock ∨ x = usedBlock)) ∨ False
    rw [usedEq, gotEq, secondEq, firstEq]
    simp [not_or, and_assoc]

#print axioms uncompress2_source
#print axioms finish_safe
end Zlib.Uncompr.Proof.LocalCompatibilityTail
