import ZlibF.Proof.«deflate.c.init.memory-total»
import ZlibF.Proof.«public-deflate-end»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec DefaultInit ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- All allocation outcomes either fail without a leak or admit actual End.
The family fixes window15/strategy0/zlib/default callbacks. The post-init
state is produced by the real initializer, rather than assumed. -/
theorem public_valid_memory_init_lifecycle {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (memory : Nat) (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (levelLow : 0 ≤ (levelValue level).toInt) (levelHigh : (levelValue level).toInt ≤ 9) :
    ∃ rc initialized,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (rc, initialized) ∧
      ((rc = Z_MEM_ERROR ∧ (∀ b, initialized.live b ↔ h.live b)) ∨
       (rc = Z_OK ∧ ∃ (ended : Heap) (zf : ZStream),
         C.run (deflateEnd (some r)) initialized = .ok (Z_OK, ended) ∧
         r.get ended = some {zf with state := none} ∧
         (∀ b, ended.live b ↔ h.live b) ∧
         ended.nalloc = h.nalloc + 5 ∧ ended.nextBlk = initialized.nextBlk)) := by
  obtain ⟨rc, initialized, actual, success | failure⟩ :=
    public_valid_memory_init_total memory fresh unique globals stream callbacks versionValue level
      memoryLow memoryHigh levelLow levelHigh
  · obtain ⟨ok, zf, sf, engine, _frequencies, _normalized, initial, _reachable, count⟩ := success
    obtain ⟨zi, si, goodI, _alloc, freeI, _level, _strategy, _window, _hash, _wrap,
      _start, _look, _pending, _bits, _header, _totalIn, _totalOut, _message,
      _frame, liveI, owned⟩ := initial
    have sameZ : zi = zf := Option.some.inj (goodI.live.hz.symm.trans engine.good.live.hz)
    have sameS : si = sf := Option.some.inj (goodI.live.hs.symm.trans engine.good.live.hs)
    subst zi
    subst si
    obtain ⟨ended, run, cleared, liveEnd, _endFrame, nalloc, next⟩ :=
      ZlibF.Spec.Public.DeflateEndProof.deflate_end_public initialized r h.nextBlk zf sf engine.good freeI
    have runOK : C.run (deflateEnd (some r)) initialized = .ok (Z_OK, ended) := by
      simpa only [engine.status, show INIT_STATE ≠ BUSY_STATE from by decide, ite_false] using run
    refine ⟨rc, initialized, actual, Or.inr ⟨ok, ended, zf, runOK, cleared, ?_, nalloc.trans count, next⟩⟩
    intro b
    have disjoint : h.live b → ¬ DeflateOwned h.nextBlk sf b := by
      intro old created
      have lower := ((owned b).mp created).1
      have upper := fresh.lt old
      omega
    constructor
    · intro alive
      obtain ⟨inited, notOwned⟩ | impossible := (liveEnd b).mp alive
      · obtain old | created := (liveI b).mp inited
        · exact old.1
        · exact False.elim (notOwned created)
      · exact False.elim impossible
    · intro old
      exact (liveEnd b).mpr (Or.inl ⟨(liveI b).mpr (Or.inl ⟨old, fun impossible => impossible⟩), disjoint old⟩)
  · obtain ⟨memoryError, _frame, _shape, live, _attempts⟩ := failure
    exact ⟨rc, initialized, actual, Or.inl ⟨memoryError, live⟩⟩

end Zlib.Deflate.Proofs.MemoryInit

#print axioms Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_lifecycle
