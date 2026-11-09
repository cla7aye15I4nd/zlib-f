import ZlibF.Proof.«uncompr.c.local-compat-prefix-facts»
import ZlibF.Proof.«uncompr.c.local-compat-continuation»

/-! Actual traditional counted utility: both real prefix allocations, counted
callee, ordered external stores and both final frees on a single execution. -/
namespace Zlib.Uncompr.Proof.LocalLegacyCutoff
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.LocalCompatPrefix
open Zlib.Uncompr.Proof.CallerObjects
set_option autoImplicit false

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

theorem uncompress2_memory_at_cutoff (h : Heap) (callerCutoff : Nat) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (unique : UniqueFrom h callerCutoff) (age : callerCutoff ≤ h.nextBlk)
    (globals : LibraryGlobals h)
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
      UniqueFrom after callerCutoff ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  let prepared := preparedHeap h capacity n
  have fresh0 := prepared_fresh h capacity n fresh
  have unique0 := prepared_uniqueFrom_of h capacity n callerCutoff fresh unique
  have globals0 := prepared_globals h capacity n globals
  have fit0 := prepared_platform h capacity n platform
  have gotCell := prepared_got_cell h capacity n fresh
  have usedCell := prepared_used_cell h capacity n
  have sourceCell0 := prepared_old_cell h capacity n fresh sourceLen n inputCell
  have destCell0 := prepared_old_cell h capacity n fresh destLen capacity outputCell
  have oldBytes := prepared_old_bytes h capacity n fresh
  have oldWritable := prepared_old_writable h capacity n fresh
  have prefixLive : LiveChange h prepared
      (fun x => x = h.nextBlk ∨ x = h.nextBlk + 1) (fun _ => False) := by
    intro x
    simpa only [LiveChange, not_false_eq_true, and_true] using prepared_live h capacity n x
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, produced, run, sourceFinal, destFinal, inputBound, outputBound,
    removed, uniqueFinal, freshFinal, fitFinal⟩ :=
    LocalCompatibilityContinuation.continuation_safe prepared callerCutoff h.nextBlk (h.nextBlk + 1) dest destLen source sourceLen n capacity xs
      fresh0 unique0 globals0 (by omega) (by omega) fit0 sourceCell0 destCell0 gotCell usedCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate gotOutput usedOutput sourceOutput destOutput (by omega) cellSeparate
      sourceGot sourceUsed destGot destUsed validInput validOutput
  refine ⟨rc, after, consumed, produced, ?_, sourceFinal, destFinal, inputBound, outputBound,
    ?_, uniqueFinal, freshFinal, fitFinal⟩
  · rw [uncompress2_to_continuation h dest destLen source sourceLen capacity n fresh outputCell inputCell]
    exact run
  · intro x
    have start := prefixLive x
    have finish := removed x
    constructor
    · intro live
      obtain ⟨middle, outside⟩ := (finish.mp live).resolve_right (by simp)
      rcases start.mp middle with ⟨old, _⟩ | temporary
      · exact Or.inl ⟨old, by simp⟩
      · exact False.elim (outside temporary)
    · rintro (⟨old, _⟩ | impossible)
      · have below := fresh.lt old
        exact finish.mpr (Or.inl ⟨start.mpr (Or.inl ⟨old, by simp⟩), by omega⟩)
      · exact False.elim impossible

#print axioms uncompress2_memory_at_cutoff
end Zlib.Uncompr.Proof.LocalLegacyCutoff
