import ZlibF.Proof.«deflate.c.init.memory-failure»
import ZlibF.Proof.«deflate.c.init.memory-frequencies»

namespace Zlib.Deflate.Proofs.MemoryInit
open C Zlib.Deflate Zlib.Deflate.Spec DefaultInit ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (InitialFrequencies)
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- The selected valid initialization family includes every allocation oracle.
Success establishes the memory-aware engine and real initial frequencies.
Failure keeps precisely the original live objects and the old-object frame.
Window 15, strategy zero, zlib wrapping and default callbacks are explicit.
This is an internal family theorem, not the unrestricted public Init2 goal. -/
theorem public_valid_memory_init_total {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (memory : Nat) (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (stream : r.get h = some z) (callbacks : DefaultOrNull z)
    (versionValue : VersionValue h version (some 49)) (level : Int32)
    (memoryLow : 1 ≤ memory) (memoryHigh : memory ≤ 9)
    (levelLow : 0 ≤ (levelValue level).toInt) (levelHigh : (levelValue level).toInt ≤ 9) :
    ∃ rc after,
      C.run (deflateInit2_ (some r) level 8 15 (Int32.ofInt memory) 0 version 112) h = .ok (rc, after) ∧
      ((rc = Z_OK ∧ ∃ zf sf,
        MemoryInitStart memory after r h.nextBlk zf sf ∧
        InitialFrequencies sf.dyn_ltree sf.dyn_dtree ∧ sf.level = levelValue level ∧
        DeflateInitial h after r (settings memory (levelValue level)) ∧
        StreamReachable .deflate after r ∧ after.nalloc = h.nalloc + 5) ∨
      (rc = Z_MEM_ERROR ∧ Frame h after (StreamRoot r) ∧ Shape h after ∧
        (∀ b, after.live b ↔ h.live b) ∧
        ((after.nalloc = h.nalloc + 1 ∧ r.get after = some (preparedStream z)) ∨
         (after.nalloc = h.nalloc + 5 ∧ ∃ zf, r.get after = some zf ∧ zf.state = none)))) := by
  classical
  by_cases stateOk : h.allocOk h.nalloc = true
  · by_cases allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true
    · obtain ⟨after, zf, sf, run, engine, frequencies, normalized, initial, reachable, count⟩ :=
        public_success_engine_frequencies memory fresh unique globals stream callbacks versionValue level
          memoryLow memoryHigh levelLow levelHigh allok
      exact ⟨Z_OK, after, run, Or.inl ⟨rfl, zf, sf, engine, frequencies, normalized, initial, reachable, count⟩⟩
    · have failure : ∃ j, j < 5 ∧ h.allocOk (h.nalloc + j) = false := by
        by_cases found : ∃ j, j < 5 ∧ h.allocOk (h.nalloc + j) = false
        · exact found
        apply False.elim
        apply allok
        intro j bound
        cases value : h.allocOk (h.nalloc + j) with
        | false => exact False.elim (found ⟨j, bound, value⟩)
        | true => rfl
      obtain ⟨j, bound, failed⟩ := failure
      have nonzero : j ≠ 0 := by
        intro zero
        subst j
        simp only [Nat.add_zero, stateOk] at failed
        contradiction
      obtain ⟨msg, run, cleared, frame, shape, count, ledger, disjoint, release⟩ :=
        public_buffer_failure_cleanup memory fresh stream callbacks versionValue level
          memoryLow memoryHigh levelLow levelHigh stateOk ⟨j, by omega, bound, failed⟩
      refine ⟨Z_MEM_ERROR, _, run, Or.inr ⟨rfl, frame, shape, ?_, Or.inr ⟨count, _, cleared, rfl⟩⟩⟩
      intro b
      rw [release b, ledger b]
      constructor
      · rintro ⟨old | created, notBorn⟩
        · exact old
        · exact False.elim (notBorn created)
      · intro old
        exact ⟨Or.inl old, fun created => disjoint b created old⟩
  · have stateFailed : h.allocOk h.nalloc = false := by
      cases value : h.allocOk h.nalloc with
      | false => rfl
      | true => exact False.elim (stateOk value)
    let after := {r.put h (preparedStream z) with nalloc := h.nalloc + 1}
    have run := public_state_allocation_failure stream callbacks versionValue level memory
      memoryLow memoryHigh levelLow levelHigh stateFailed
    have shape : Shape h after := by
      simpa only [Shape, after] using shape_put stream (preparedStream z)
    have frame : Frame h after (StreamRoot r) := by
      obtain ⟨statics, oracle, garbage, next, _count, old⟩ := frame_put r (preparedStream z) fresh
      exact ⟨statics, oracle, garbage, next, by simp [after], old⟩
    refine ⟨Z_MEM_ERROR, after, run, Or.inr ⟨rfl, frame, shape, shape.live, Or.inl ⟨rfl, ?_⟩⟩⟩
    simpa only [after, ZStreamRef.get] using ZStreamRef.get_put_same stream (preparedStream z)

end Zlib.Deflate.Proofs.MemoryInit

#print axioms Zlib.Deflate.Proofs.MemoryInit.public_valid_memory_init_total
