import ZlibF.Proof.«deflate.c.engine.memory-fast-boundary»
import ZlibF.Spec.Public.Domains
import ZlibF.Spec.Functional.Api.Compress

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.MemoryInit (MemoryInitStart)
set_option autoImplicit false

/-- Every real successful construction at fast level one through three
establishes the complete empty parameterized content on the returned heap.
The allocation-oracle facts are explicit; no initialized invariant or
callee execution contract is a premise. -/
theorem memory_fast_initialization {memory : Nat} {h : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (levelLow : 1 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 3)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, after) ∧
      MemoryInitStart memory after r h.nextBlk zf sf ∧
      MemoryFastBoundary memory after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      sf.level = DefaultInit.levelValue level ∧
      DeflateInitial h after r (MemoryInit.settings memory (DefaultInit.levelValue level)) ∧
      StreamReachable .deflate after r ∧ after.nalloc = h.nalloc + 5 := by
  obtain ⟨fresh, unique, globals, versionValue, z, stream, callbacks, _state⟩ := domain
  obtain ⟨after, zf, sf, run, start, frequencies, levelEq, initial, reachable, count⟩ :=
    MemoryInit.public_success_engine_frequencies memory fresh unique globals stream callbacks versionValue
      level memoryLow memoryHigh (by omega) (by omega) allok
  obtain ⟨clearHeap, clearZ, clearState, clearRun, clearStart, clear, _level, _initial, _reachable, _count⟩ :=
    MemoryInit.public_success_engine_block_clear memory fresh unique globals stream callbacks versionValue
      level memoryLow memoryHigh (by omega) (by omega) allok
  have heaps : clearHeap = after := (Prod.mk.inj (Except.ok.inj (clearRun.symm.trans run))).2
  subst clearHeap
  have states : clearState = sf := Option.some.inj (clearStart.good.live.hs.symm.trans start.good.live.hs)
  subst clearState
  have header : sf.gzhead = none := by
    obtain ⟨zi, si, good, _alloc, _free, _lev, _strategy, _win, _hash, _status, _start,
      _look, _pending, _bits, header, _rest⟩ := initial
    have same : si = sf := Option.some.inj (good.live.hs.symm.trans start.good.live.hs)
    simpa only [same] using header
  have boundary := MemoryFastBoundary.initial start frequencies clear
    (by rw [levelEq]; exact levelLow) (by rw [levelEq]; exact levelHigh) header input
  exact ⟨after, zf, sf, run, start, boundary, levelEq, initial, reachable, count⟩

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- Each of the nine memory levels and each fast compression level has
an actual public initializer witness, with its derived content boundary.
Method eight, window fifteen, strategy zero, zlib wrapping and default-or-null
callbacks are fixed. This witnesses initialization, not compression execution. -/
theorem memory_fast_initialization_witness (memory : Nat) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (flag : level = 1 ∨ level = 2 ∨ level = 3) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some (.tab 0)) level 8 15 (Int32.ofInt memory) 0 (.ref (.blk 1) 0) 112)
        ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap = .ok (Z_OK, after) ∧
      MemoryFastBoundary memory after (.tab 0) 2 zf sf (fun _ => 0) 0 0 [] (engineConfig sf) ∧
      sf.level = level ∧ StreamReachable .deflate after (.tab 0) := by
  have domain : InitDomain ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap (.tab 0) (.ref (.blk 1) 0) :=
    ⟨witness_fresh, witness_uniq, rfl, witness_version, default,
      by simp [ZStreamRef.get, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap], ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  have levelValue : DefaultInit.levelValue level = level := by
    rcases flag with rfl | rfl | rfl <;> rfl
  have low : 1 ≤ (DefaultInit.levelValue level).toInt := by
    rw [levelValue]; rcases flag with rfl | rfl | rfl <;> decide
  have high : (DefaultInit.levelValue level).toInt ≤ 3 := by
    rw [levelValue]; rcases flag with rfl | rfl | rfl <;> decide
  obtain ⟨after, zf, sf, run, _start, boundary, levelEq, _initial, reachable, _count⟩ :=
    memory_fast_initialization domain memoryLow memoryHigh level low high (by intro j _; rfl) (fun _ => 0)
  exact ⟨after, zf, sf, run, boundary, levelEq.trans levelValue, reachable⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_initialization
#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_initialization_witness
