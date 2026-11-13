import ZlibF.Proof.«deflate.c.engine.public-first-partial-sync»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»

/-! # The initialized default protocol is closed under PARTIAL/SYNC requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual active default PARTIAL/SYNC calls preserve the same initialized
protocol as ordinary calls, including first headers, old pending bytes
and empty-input duplicates. The non-FINISH guard is handled separately
by partial_sync_total; it is not excluded from the complete request theorem. -/
theorem DefaultFinishBoundary.partial_sync_active {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (active : d.status ≠ FINISH_STATE)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_BUF_ERROR) := by
  have executed : ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR) ∧ PublicFinishPhase after r ds z' result config ∧
      (result.last_flush = flush ∨ result.last_flush = -1) := by
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨used, produced, after, z', result, extended, nextOrigin, nextBase, ys,
          run, stateA, buffersA, accountA, statusA, lastA⟩ :=
        public_default_first_partial_sync_buffered start level state buffers pointer output boundary.configuration.memory valid flush flag
      exact ⟨used, produced, Z_OK, after, z', result, run, stateA.good, buffersA, accountA,
        Or.inl rfl, Or.inl ⟨extended, nextOrigin, nextBase, ys, stateA, statusA⟩, lastA⟩
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨used, produced, rc, after, z', result, extended, nextOrigin, nextBase, ys,
          run, stateA, buffersA, accountA, allowed, statusA, lastA⟩ :=
        public_default_busy_partial_sync_buffered state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper flush flag
      exact ⟨used, produced, rc, after, z', result, run, stateA.good, buffersA, accountA,
        allowed, Or.inl ⟨extended, nextOrigin, nextBase, ys, stateA, statusA⟩, lastA⟩
    · exact False.elim (active finishing.status)
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, phaseA, lastA⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) flush) (value := rc) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases lastA with eq | eq
    · rcases flag with rfl | rfl <;> rw [eq] <;> decide
    · rw [eq]; decide
  exact ⟨used, produced, rc, after, z', result, run,
    ⟨goodA, reachableA, boundary.configuration, Or.inr phaseA, bounds.1, bounds.2⟩,
    buffersA, accountA, allowed⟩

/-- Every default PARTIAL/SYNC request with null or raw caller output returns
and preserves the initialized protocol. It includes all capacities, input
lengths, pending states, duplicate requests, pointer-argument refusals and
PARTIAL/SYNC after FINISH_STATE. Other valid flags and advanced operations remain
separate; this does not replace Goal.deflate or prove encoded history. -/
theorem DefaultFinishBoundary.partial_sync_total {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl <;> decide
  have nonfinal : flush ≠ Z_FINISH := by rcases flag with rfl | rfl <;> decide
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨err, after, z', allowed, run, stateA, buffersA, accountA⟩ :=
      boundary.entry_refusals flush buffers flagLo flagHi refused
    exact ⟨0, 0, err, after, z', d, run, stateA, buffersA, accountA, Or.inr allowed⟩
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null :=
      fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have nonzeroNat : z.avail_out.toNat ≠ 0 := fun eq => nonzero (UInt32.toNat_inj.mp eq)
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    have active : d.status ≠ FINISH_STATE := fun status =>
      refused (Or.inr (Or.inr (Or.inl ⟨status, nonfinal⟩)))
    obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed⟩ :=
      boundary.partial_sync_active buffers pointer output valid active flush flag
    refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, ?_⟩
    exact allowed.elim Or.inl (fun err => Or.inr (Or.inr err))

end Zlib.Deflate.Engine.Proofs
