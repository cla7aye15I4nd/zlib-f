import ZlibF.Proof.«deflate.c.engine.memory-slow-boundary»
import ZlibF.Spec.Public.Domains

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.MemoryInit (MemoryInitStart)
set_option autoImplicit false

/-- Every real successful construction at slow level four through nine
establishes the complete empty parameterized content on the returned heap.
The allocation-oracle facts are explicit; no initialized invariant or
callee execution contract is a premise. -/
theorem memory_slow_initialization {memory : Nat} {h : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (levelLow : 4 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 9)
    (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (Z_OK, after) ∧
      MemoryInitStart memory after r h.nextBlk zf sf ∧
      MemorySlowBoundary memory after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
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
  have boundary := MemorySlowBoundary.initial start frequencies clear
    (by rw [levelEq]; exact levelLow) (by rw [levelEq]; exact levelHigh) header input
  exact ⟨after, zf, sf, run, start, boundary, levelEq, initial, reachable, count⟩

open ZlibF.Spec.Public.Proofs.DeflateInit in
/-- Every memory level one through nine and normalized slow level four
through nine has a real initializer witness and derived content boundary.
The default level minus one is included through its normalization to six. -/
theorem memory_slow_initialization_witness (memory : Nat) (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (level : Int32) (levelLow : 4 ≤ (DefaultInit.levelValue level).toInt)
    (levelHigh : (DefaultInit.levelValue level).toInt ≤ 9) :
    ∃ after zf sf,
      C.run (deflateInit2_ (some (.tab 0)) level 8 15 (Int32.ofInt memory) 0 (.ref (.blk 1) 0) 112)
        ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap = .ok (Z_OK, after) ∧
      MemorySlowBoundary memory after (.tab 0) 2 zf sf (fun _ => 0) 0 0 [] (engineConfig sf) ∧
      sf.level = DefaultInit.levelValue level ∧ StreamReachable .deflate after (.tab 0) := by
  have domain : InitDomain ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap (.tab 0) (.ref (.blk 1) 0) :=
    ⟨witness_fresh, witness_uniq, rfl, witness_version, default,
      by simp [ZStreamRef.get, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap], ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  obtain ⟨after, zf, sf, run, _start, boundary, levelEq, _initial, reachable, _count⟩ :=
    memory_slow_initialization domain memoryLow memoryHigh level levelLow levelHigh
      (by intro j _; rfl) (fun _ => 0)
  exact ⟨after, zf, sf, run, boundary, levelEq, reachable⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_slow_initialization
#print axioms Zlib.Deflate.Engine.Proofs.memory_slow_initialization_witness
