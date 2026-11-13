import ZlibF.Proof.«deflate.c.engine.common-no-flush-accepted»
import ZlibF.Proof.«deflate.c.engine.common-finish-protocol»

/-! # Accepted NO_FLUSH retains the common initialized phase boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- New input, pending publication and permitted empty retries retain
the same common invariant used by finite FINISH completion. -/
theorem CommonSlowFinishBoundary.no_flush_resuming {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (resume : d.status = BUSY_STATE → d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (unfinished : d.status ≠ FINISH_STATE) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      CommonSlowFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE := by
  have executed : ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
    rcases boundary.phase with working | finishing
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = config.level := congrArg EngineConfig.level state.configuration
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_common_slow_busy_no_flush_accepted state buffers status
        (by rw [level]; exact boundary.configuration.level_low)
        (by rw [level]; exact boundary.configuration.level_high) strategy pointer output
        boundary.configuration.memory boundary.configuration.wrap valid (resume status) boundary.lower boundary.upper
    · exact False.elim (unfinished finishing.status)
  obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys,
    run, stateA, buffersA, accountA, statusA, lastA⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_NO_FLUSH) (value := Z_OK) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases lastA with eq | eq <;> rw [eq] <;> decide
  exact ⟨used, produced, after, z', result, run,
    ⟨stateA.good, reachableA, boundary.configuration,
      Or.inl ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA⟩, bounds.1, bounds.2⟩,
    buffersA, accountA, statusA⟩

end Zlib.Deflate.Engine.Proofs
