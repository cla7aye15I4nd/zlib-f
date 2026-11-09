import ZlibF.Proof.«uncompr.c.compat-continuation»
import ZlibF.Proof.«uncompr.c.legacy-prefix»

/-!
# Actual compatibility counted-wrapper memory safety

The real two-allocation prefix feeds the real counted callee on its returned
heap. Exact external-cell observations support the original ordered writebacks
and both temporary frees. All allocator outcomes retain caller cells, bounded
returned values and a fresh, unique heap with no allocation residue. Independent
format correctness and the complete public Frame/Store contract remain open.
-/

namespace Zlib.Uncompr.Proof.LegacyMemory
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.CompatPrefix Zlib.Uncompr.Proof.CompatibilityContinuation
open Zlib.Uncompr.Proof.CallerObjects

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

/-- The original two allocations precede both initial stores. The same heap
feeds the actual counted callee, external stores and both temporary frees. -/
theorem uncompress2_memory (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
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
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨prepared, prefixRun, fresh0, unique0, globals0, fit0, gotCell, usedCell,
    sourceCell0, destCell0, _next, _nalloc, _oracle, prefixLive, _views, oldBytes, oldWritable⟩ :=
    prepare_boundary h destLen sourceLen n capacity fresh uniq globals platform inputCell outputCell
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, produced, run, sourceFinal, destFinal, inputBound, outputBound,
    removed, uniqueFinal, freshFinal, fitFinal⟩ :=
    continuation_safe prepared h.nextBlk (h.nextBlk + 1) dest destLen source sourceLen n capacity xs
      fresh0 unique0 globals0 fit0 sourceCell0 destCell0 gotCell usedCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate gotOutput usedOutput sourceOutput destOutput (by omega) cellSeparate
      sourceGot sourceUsed destGot destUsed validInput validOutput
  refine ⟨rc, after, consumed, produced, ?_, sourceFinal, destFinal, inputBound, outputBound,
    ?_, uniqueFinal, freshFinal, fitFinal⟩
  · rw [uncompress2_after_prepare h prepared dest destLen source sourceLen _ _ prefixRun]
    simpa only [C.run, continuation, CompatPrefix.finish, Zlib.Uncompr.Proof.CompatibilityTail.finish] using run
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

#print axioms uncompress2_memory
end Zlib.Uncompr.Proof.LegacyMemory
