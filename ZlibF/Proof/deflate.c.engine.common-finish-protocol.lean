import ZlibF.Proof.«deflate.c.engine.common-slow-public»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»

/-! # FINISH phase preservation for compression levels four through nine -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Standard memory, window and wrapper with any slow compression level. -/
structure CommonSlowFinishConfig (config : EngineConfig) : Prop where
  level_low : 4 ≤ config.level.toInt
  level_high : config.level.toInt ≤ 9
  strategy : config.strategy = 0
  memory : config.memory.toNat = 16384
  window : config.windowBits = 15
  hash : config.hashBits = 15
  wrap : config.wrap = 1
  header : config.header = none

/-- The actual post-header working or finishing state. Initialization
and its real split-header call establish this boundary separately. -/
structure CommonSlowFinishBoundary (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) : Prop where
  good : DGood h r ds z d
  reachable : StreamReachable .deflate h r
  configuration : CommonSlowFinishConfig config
  phase : PublicFinishPhase h r ds z d config
  lower : -2 ≤ d.last_flush.toInt
  upper : d.last_flush.toInt ≤ 5

theorem CommonSlowFinishBoundary.no_header {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) : d.gzhead = none := by
  rcases boundary.phase with ⟨_input, _origin, _base, _xs, state, _status⟩ | finishing
  · exact (congrArg EngineConfig.header state.configuration).trans boundary.configuration.header
  · exact (congrArg EngineConfig.header finishing.configuration).trans boundary.configuration.header

/-- Legal caller edits retain the same post-header boundary and level. -/
theorem CommonSlowFinishBoundary.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ CommonSlowFinishBoundary g r ds zg d config := by
  obtain ⟨zg, getG, _fields, goodG⟩ := rebuffer_good_no_header boundary.good edit boundary.no_header
  refine ⟨zg, getG, goodG, StreamReachable.rebuffer boundary.reachable edit (fun k => nomatch k),
    boundary.configuration, ?_, boundary.lower, boundary.upper⟩
  rcases boundary.phase with ⟨input, origin, base, xs, state, status⟩ | finishing
  · obtain ⟨other, getB, stateG⟩ := rebuffer_buffered_boundary state edit boundary.no_header
    have same : other = zg := Option.some.inj (getB.symm.trans getG)
    subst other
    exact Or.inl ⟨input, origin, base, xs, stateG, status⟩
  · exact Or.inr finishing

/-- The complete accepted public FINISH preserves the same common-level
phase boundary. Working, pending-full, finishing and trailer-drain paths
are real executions. New input after FINISH_STATE is excluded by the
documented FINISH protocol. Refusals and other flushes are separate. -/
theorem CommonSlowFinishBoundary.finish {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : CommonSlowFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CommonSlowFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have executed : ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      PublicFinishPhase after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
    rcases boundary.phase with ⟨input, origin, base, xs, state, status⟩ | finishing
    · have level : d.level = config.level := congrArg EngineConfig.level state.configuration
      have strategy : d.strategy = 0 :=
        (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed,
          _bitsA, phaseA, lastA, ended⟩ := public_common_slow_busy_finish_phase state buffers status
        (by rw [level]; exact boundary.configuration.level_low)
        (by rw [level]; exact boundary.configuration.level_high) strategy pointer
        boundary.configuration.memory boundary.configuration.wrap output valid boundary.lower boundary.upper
      exact ⟨used, produced, rc, after, z', result, run, goodA, phaseA, buffersA, accountA, allowed, lastA, ended⟩
    · obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed,
          phaseA, lastA, emptyA, ended⟩ := public_default_finishing_phase boundary.good buffers
        finishing pointer (accepted finishing.status) output boundary.lower boundary.upper
      exact ⟨0, produced, rc, after, z', result, run, goodA, Or.inr phaseA, buffersA, accountA,
        allowed, lastA, fun done => ⟨phaseA.status, (ended done).1, emptyA,
          phaseA.lookahead, (ended done).2, phaseA.bits⟩⟩
  obtain ⟨used, produced, rc, after, z', result, run, goodA, phaseA, buffersA, accountA,
    allowed, lastA, ended⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases lastA with last | last <;> rw [last] <;> decide
  exact ⟨used, produced, rc, after, z', result, run,
    ⟨goodA, reachableA, boundary.configuration, phaseA, bounds.1, bounds.2⟩,
    buffersA, accountA, allowed, ended⟩

end Zlib.Deflate.Engine.Proofs
