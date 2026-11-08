import ZlibF.Proof.«deflate.c.engine.common-finish-protocol»
import ZlibF.Proof.«deflate.c.engine.common-busy-finish-storage»
import ZlibF.Proof.«deflate.c.engine.finishing-full-storage»

/-! # Complete accepted common-level FINISH resource and total-counter effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual call retains both cumulative counters and all allocation,
object and external-memory effects, in either public FINISH phase. -/
theorem CommonSlowFinishBoundary.finish_storage_execution
    {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases boundary.phase with ⟨input, origin, base, xs, state, status⟩ | finishing
  · have level : d.level = config.level := congrArg EngineConfig.level state.configuration
    have strategy : d.strategy = 0 :=
      (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
    exact public_common_slow_busy_finish_full_storage state buffers status
      (by rw [level]; exact boundary.configuration.level_low)
      (by rw [level]; exact boundary.configuration.level_high) strategy pointer
      boundary.configuration.memory boundary.configuration.wrap output valid boundary.lower boundary.upper
  · obtain ⟨produced, rc, after, z', result, run, goodA, accountA, inputA, outputA,
        shapeA, frameA, liveA, allocA, nextA⟩ :=
      public_finishing_full_storage_execution boundary.good buffers finishing pointer
        (accepted finishing.status) output boundary.lower boundary.upper
    exact ⟨0, produced, rc, after, z', result, run, goodA, accountA,
      by simpa only [show UInt64.ofNat 0 = (0 : UInt64) from rfl, UInt64.add_zero] using inputA,
      outputA, shapeA, frameA, liveA, allocA, nextA⟩

/-- These are effects of the same observed run, by execution determinism. -/
theorem CommonSlowFinishBoundary.finish_run_full_storage
    {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (actual : deflate (some r) Z_FINISH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_used, _produced, _rc, computed, _z, _d, run, _good, _account, _in, _out,
      shape, frame, live, alloc, next⟩ := boundary.finish_storage_execution buffers pointer output valid accepted
  have same := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  subst computed
  exact ⟨shape, frame, live, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
