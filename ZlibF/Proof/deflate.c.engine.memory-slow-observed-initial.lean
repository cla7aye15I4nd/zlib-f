import ZlibF.Proof.«deflate.c.engine.memory-slow-initial»
import ZlibF.Proof.«deflate.c.init.memory-failure»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Observed success of the actual constructor derives all five allocation
choices; they are not assumptions of the initialized history. -/
theorem memory_success_allocation_choices {memory : Nat} {before after : Heap}
    {r : ZStreamRef} {version : BPtr} (domain : InitDomain before r version)
    (low : 1 ≤ memory) (high : memory ≤ 9) (level : Int32)
    (levelLow : 0 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 9)
    (actual : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) before =
      .ok (Z_OK, after)) : ∀ j, j < 5 → before.allocOk (before.nalloc + j) = true := by
  obtain ⟨fresh, _unique, _globals, versionValue, z, stream, callbacks, _empty⟩ := domain
  by_cases stateOk : before.allocOk before.nalloc = true
  · by_cases allok : ∀ j, j < 5 → before.allocOk (before.nalloc + j) = true
    · exact allok
    · have failed : ∃ j, j < 5 ∧ before.allocOk (before.nalloc + j) = false := by
        by_cases found : ∃ j, j < 5 ∧ before.allocOk (before.nalloc + j) = false
        · exact found
        · exact False.elim (allok (by
            intro j below
            cases choice : before.allocOk (before.nalloc + j) with
            | false => exact False.elim (found ⟨j, below, choice⟩)
            | true => rfl))
      obtain ⟨j, below, failed⟩ := failed
      have nonzero : j ≠ 0 := by
        intro zero
        subst j
        simp only [Nat.add_zero, stateOk] at failed
        contradiction
      obtain ⟨_message, run, _rest⟩ := MemoryInit.public_buffer_failure_cleanup memory
        fresh stream callbacks versionValue level low high levelLow levelHigh stateOk
        ⟨j, by omega, below, failed⟩
      have impossible := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      exact False.elim ((show Z_MEM_ERROR ≠ Z_OK from by decide) impossible)
  · have failed : before.allocOk before.nalloc = false := by
      cases choice : before.allocOk before.nalloc with
      | false => rfl
      | true => exact False.elim (stateOk choice)
    have run := MemoryInit.public_state_allocation_failure stream callbacks versionValue level memory
      low high levelLow levelHigh failed
    have impossible := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
    exact False.elim ((show Z_MEM_ERROR ≠ Z_OK from by decide) impossible)

/-- Every observed successful actual Init2 establishes the strong slow
boundary on that returned heap, for all memory levels one through nine.
This internal theorem fixes method eight, window fifteen, strategy zero,
zlib wrapping and default-or-null callbacks. Normalized levels four through
nine include the default minus-one level after normalization.
The allocation oracle is arbitrary. Representation and allocation facts
come from the actual constructor, not extra caller hypotheses. -/
theorem memory_slow_observed_initialization {memory : Nat} {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} (domain : InitDomain before r version)
    (low : 1 ≤ memory) (high : memory ≤ 9) (level : Int32)
    (levelLow : 4 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 9)
    (actual : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) before =
      .ok (Z_OK, initialized)) (input : Nat → UInt8) :
    ∃ zf sf,
      MemoryInit.MemoryInitStart memory initialized r before.nextBlk zf sf ∧
      MemorySlowBoundary memory initialized r before.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      sf.level = DefaultInit.levelValue level ∧
      DeflateInitial before initialized r (MemoryInit.settings memory (DefaultInit.levelValue level)) ∧
      StreamReachable .deflate initialized r ∧ initialized.nalloc = before.nalloc + 5 := by
  have allok := memory_success_allocation_choices domain low high level (by omega) levelHigh actual
  obtain ⟨computed, zf, sf, run, initial, boundary, normalized, relation, reachable, count⟩ :=
    memory_slow_initialization domain low high level levelLow levelHigh allok input
  have heaps : computed = initialized := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  subst computed
  exact ⟨zf, sf, initial, boundary, normalized, relation, reachable, count⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_success_allocation_choices
#print axioms Zlib.Deflate.Engine.Proofs.memory_slow_observed_initialization
