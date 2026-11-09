import ZlibF.Proof.«uncompr.c.scalar-writeback»
import ZlibF.Proof.«uncompr.c.single-length»

/-!
# The actual compatibility-wrapper writeback and cleanup

The complete source equation retains both allocations before both initial
stores. After the counted callee returns, the two real external scalar stores
precede both temporary frees. The same returning heap supplies exact scalar
values, ordered Stores, final cells and the two-object removal ledger. Full
prefix/callee composition and public format correctness remain separate.
-/

namespace Zlib.Uncompr.Proof.CompatibilityTail
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.ScalarWriteback Zlib.Uncompr.Proof.Cells

/-- The original post-callee scalar writeback and automatic cleanup. -/
def finish (destLen sourceLen got used : BPtr) (rc : Int32) : M Int32 := do
  store64 sourceLen (← load64 used)
  store64 destLen (← load64 got)
  freeB got
  freeB used
  return rc

/-- The complete original function keeps both allocations before both scalar
writes. The extracted tail is definitionally connected to the actual source. -/
theorem uncompress2_source : uncompress2 = (fun dest destLen source sourceLen => do
    let got ← allocLocal 8
    let used ← allocLocal 8
    store64 got (← load64 destLen)
    store64 used (← load64 sourceLen)
    let rc ← uncompress2_z dest got source used
    finish destLen sourceLen got used rc) := by
  unfold uncompress2 finish
  with_reducible rfl

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

/-- The actual outer stores precede the two temporary frees. -/
theorem finish_safe (h : Heap) (gotBlock usedBlock : Nat) (destLen sourceLen : BPtr)
    (sourceOld destOld gotValue usedValue : UInt64) (rc : Int32)
    (uniq : Uniq h) (fresh : Fresh h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
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
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  have srcGot := outside_separate sourceLen 8 gotBlock sourceGot
  have srcUsed := outside_separate sourceLen 8 usedBlock sourceUsed
  have dstGot := outside_separate destLen 8 gotBlock destGot
  have dstUsed := outside_separate destLen 8 usedBlock destUsed
  obtain ⟨first, sourceRun, sourceStore, writtenSource, sourceLive, unique1, fresh1, fit1, keep1⟩ :=
    writable_scalar_store h sourceLen usedValue sourceCell.2 uniq fresh platform
  have got1 := keep1 (.ref (.blk gotBlock) 0) gotValue gotCell (separate_symm _ _ _ _ srcGot)
  have used1 := keep1 (.ref (.blk usedBlock) 0) usedValue usedCell (separate_symm _ _ _ _ srcUsed)
  have dest1 := keep1 destLen destOld destCell (separate_symm _ _ _ _ separate)
  obtain ⟨second, destRun, destStore, writtenDest, destLive, unique2, fresh2, fit2, keep2⟩ :=
    writable_scalar_store first destLen gotValue dest1.2 unique1 fresh1 fit1
  have source2 := keep2 sourceLen usedValue writtenSource separate
  have got2 := keep2 (.ref (.blk gotBlock) 0) gotValue got1 (separate_symm _ _ _ _ dstGot)
  have used2 := keep2 (.ref (.blk usedBlock) 0) usedValue used1 (separate_symm _ _ _ _ dstUsed)
  obtain ⟨freeGot, gotLive⟩ := free_scalar second gotBlock gotValue unique2 got2
  have unique3 := freed_uniq second gotBlock unique2
  have fresh3 := freed_fresh second gotBlock fresh2
  have fit3 := Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform second gotBlock fit2
  have used3 := freed_cell second gotBlock (.ref (.blk usedBlock) 0) usedValue used2 (by
    intro off same
    have blocks : usedBlock = gotBlock := BRef.blk.inj (Ptr.ref.inj same).1
    exact distinct blocks.symm)
  obtain ⟨freeUsed, usedLive⟩ := free_scalar (freedHeap second gotBlock) usedBlock usedValue unique3 used3
  let final := freedHeap (freedHeap second gotBlock) usedBlock
  have sourceFinal := freed_cell (freedHeap second gotBlock) usedBlock sourceLen usedValue
    (freed_cell second gotBlock sourceLen usedValue source2 sourceGot) sourceUsed
  have destFinal := freed_cell (freedHeap second gotBlock) usedBlock destLen gotValue
    (freed_cell second gotBlock destLen gotValue writtenDest destGot) destUsed
  refine ⟨first, second, final, ?_, sourceStore, destStore, sourceFinal, destFinal, ?_,
    freed_uniq _ usedBlock unique3, freed_fresh _ usedBlock fresh3,
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
end Zlib.Uncompr.Proof.CompatibilityTail
