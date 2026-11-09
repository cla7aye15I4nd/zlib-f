import ZlibF.Proof.«deflate.c.init.memory-failure»
import ZlibF.Proof.«deflate.c.engine.memory-fast-initial»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.MemoryInit (MemoryInitStart)
set_option autoImplicit false

/-- Actual successful valid fast initialization forces each of its five
allocation-oracle outcomes. A state/buffer failure executes MEM_ERROR,
contradicting the observed successful source return; no allocation or
initialization contract is assumed by the caller. -/
theorem memory_fast_success_allocations {memory : Nat} {h observed : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (levelLow : 1 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 3)
    (actual : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, observed)) :
    ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
  obtain ⟨fresh, _unique, _globals, versionValue, z, stream, callbacks, _state⟩ := domain
  intro j below
  cases value : h.allocOk (h.nalloc + j) with
  | true => rfl
  | false =>
      exfalso
      by_cases stateOk : h.allocOk h.nalloc = true
      · have nonzero : j ≠ 0 := by
          intro zero
          subst j
          simp only [Nat.add_zero, stateOk] at value
          contradiction
        obtain ⟨msg, failedRun, _rest⟩ :=
          MemoryInit.public_buffer_failure_cleanup memory fresh stream callbacks versionValue level
            memoryLow memoryHigh (by omega) (by omega) stateOk ⟨j, by omega, below, value⟩
        have codes : Z_MEM_ERROR = Z_OK := (Prod.mk.inj (Except.ok.inj (failedRun.symm.trans actual))).1
        exact (by decide : Z_MEM_ERROR ≠ Z_OK) codes
      · have stateFailed : h.allocOk h.nalloc = false := by
          cases stateValue : h.allocOk h.nalloc with
          | false => rfl
          | true => exact False.elim (stateOk stateValue)
        have failedRun := MemoryInit.public_state_allocation_failure stream callbacks versionValue level memory
          memoryLow memoryHigh (by omega) (by omega) stateFailed
        have codes : Z_MEM_ERROR = Z_OK := (Prod.mk.inj (Except.ok.inj (failedRun.symm.trans actual))).1
        exact (by decide : Z_MEM_ERROR ≠ Z_OK) codes
/-- Actual successful initialization establishes the fast content boundary.
The family uses the explicit InitDomain, levels one through three and memory
levels one through nine. Method eight, window fifteen, strategy zero, zlib
wrapping and default-or-null callbacks are fixed. Allocation facts follow
from the observed run; no initialized invariant or callee contract is assumed.
This initialization result does not establish compression execution. -/
theorem memory_fast_observed_initialization {memory : Nat} {h observed : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (levelLow : 1 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 3)
    (actual : C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, observed)) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, after) ∧
      MemoryInitStart memory after r h.nextBlk zf sf ∧
      MemoryFastBoundary memory after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      sf.level = DefaultInit.levelValue level ∧
      DeflateInitial h after r (MemoryInit.settings memory (DefaultInit.levelValue level)) ∧
      StreamReachable .deflate after r ∧ after.nalloc = h.nalloc + 5 := by
  have allok := memory_fast_success_allocations domain memoryLow memoryHigh level levelLow levelHigh actual
  exact memory_fast_initialization domain memoryLow memoryHigh level levelLow levelHigh allok input

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_success_allocations
#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_observed_initialization
