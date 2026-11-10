import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.finish-protocol-history»

/-! # Ordinary input calls preserve the initialized FINISH protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Ordinary accepted NO_FLUSH calls with new input preserve the same
initialized protocol used by every later FINISH call. Pending output and
every positive raw output capacity are included. Empty-input duplicate
requests and requests after FINISH_STATE are separate refusal cases. -/
theorem DefaultFinishBoundary.no_flush {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (nonempty : z.avail_in ≠ 0)
    (unfinished : d.status ≠ FINISH_STATE) :
    ∃ used produced after z' result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE := by
  have executed : ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      exact public_default_first_no_flush_buffered start level state buffers pointer output boundary.configuration.memory valid
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      exact public_default_busy_no_flush_buffered state buffers status level strategy pointer output
        boundary.configuration.memory boundary.configuration.wrap valid nonempty boundary.lower boundary.upper
    · exact False.elim (unfinished finishing.status)
  obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys,
    run, stateA, buffersA, accountA, statusA, lastA⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_NO_FLUSH) (value := Z_OK) boundary.reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases lastA with eq | eq <;> rw [eq] <;> decide
  exact ⟨used, produced, after, z', result, run,
    ⟨stateA.good, reachableA, boundary.configuration,
      Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA⟩), bounds.1, bounds.2⟩,
    buffersA, accountA, statusA⟩

end Zlib.Deflate.Engine.Proofs
