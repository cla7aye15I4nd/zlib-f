import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.public-busy-finish-phase»
import ZlibF.Proof.«deflate.c.engine.public-finishing-phase»

/-! # An initialized FINISH protocol closed under actual calls and caller edits

This internal protocol covers default initialization followed by accepted
Z_FINISH calls. It is not the all-flush, all-operation public goal. Complete
output-format history, total counters and heap-frame refinement remain open.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The fixed default compression configuration used by this protocol. -/
structure DefaultFinishConfig (config : EngineConfig) : Prop where
  level : config.level = 6
  strategy : config.strategy = 0
  memory : config.memory.toNat = 16384
  wrap : config.wrap = 1
  header : config.header = none

/-- The same actual-state invariant starts at init and survives every
accepted FINISH call and legal rebuffering. Finishing needs no later
strategy call; working states retain the full content boundary. -/
structure DefaultFinishBoundary (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (config : EngineConfig) : Prop where
  good : DGood h r ds z d
  reachable : StreamReachable .deflate h r
  configuration : DefaultFinishConfig config
  phase : (∃ input origin base, EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input origin base [] config) ∨
    PublicFinishPhase h r ds z d config
  lower : -2 ≤ d.last_flush.toInt
  upper : d.last_flush.toInt ≤ 5

theorem DefaultFinishBoundary.no_header {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) : d.gzhead = none := by
  rcases boundary.phase with ⟨input, origin, base, _start, state⟩ | working | finishing
  · exact (congrArg EngineConfig.header state.configuration).trans boundary.configuration.header
  · obtain ⟨input, origin, base, xs, state, _status⟩ := working
    exact (congrArg EngineConfig.header state.configuration).trans boundary.configuration.header
  · exact (congrArg EngineConfig.header finishing.configuration).trans boundary.configuration.header

theorem default_finish_active_header {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (header : d.gzhead = none) :
    ActiveHeader h r := by
  refine ⟨z, good.live.hz, ?_, ?_⟩
  · intro i s kind _live
    rw [good.live.zst] at kind
    cases kind
  · intro i s kind live
    have keys : ds = i := by
      simpa only [good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
    subst i
    have states : s = d := Option.some.inj (live.symm.trans good.live.hs)
    subst s
    exact Or.inl header

/-- Legal caller changes retain the entire protocol, even when exhausted
output is replaced by a positive-capacity buffer. Caller ranges and the
accepted input/output guards are checked at the next call. -/
theorem DefaultFinishBoundary.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ DefaultFinishBoundary g r ds zg d config := by
  have header := boundary.no_header
  obtain ⟨zg, getG, _changed, goodG⟩ := rebuffer_good_no_header boundary.good edit header
  refine ⟨zg, getG, goodG, StreamReachable.rebuffer boundary.reachable edit, boundary.configuration, ?_,
    boundary.lower, boundary.upper⟩
  rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
  · obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit header
    obtain ⟨zb, getB, stateG⟩ := rebuffer_buffered_boundary state edit header
    have sameS : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zs zb
    exact Or.inl ⟨input, origin, base, startG, stateG⟩
  · obtain ⟨input, origin, base, xs, state, status⟩ := working
    obtain ⟨zb, getB, stateG⟩ := rebuffer_buffered_boundary state edit header
    have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
    subst zb
    exact Or.inr (Or.inl ⟨input, origin, base, xs, stateG, status⟩)
  · exact Or.inr (Or.inr finishing)

/-- The accepted real FINISH call preserves the initialized protocol and
extends the actual public reachable history. No loop bound, byte budget
or output-capacity lower bound beyond a positive public buffer is assumed.
New input after FINISH_STATE is the separate refusal case. -/
theorem DefaultFinishBoundary.finish {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  have executed : ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ PublicFinishPhase after r ds z' result config ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, _bits, phaseA, last, ended⟩ :=
        public_default_first_finish_phase start level state buffers pointer output boundary.configuration.memory valid
      exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, _bits, phaseA, last, ended⟩ :=
        public_default_busy_finish_phase state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩
    · obtain ⟨produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, emptyA, ended⟩ :=
        public_default_finishing_phase boundary.good buffers finishing pointer (accepted finishing.status) output boundary.lower boundary.upper
      exact ⟨0, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, Or.inr phaseA, last,
        fun done => ⟨phaseA.status, (ended done).1, emptyA, phaseA.lookahead, (ended done).2, phaseA.bits⟩⟩
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, phaseA, last, ended⟩ := executed
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) boundary.reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simpa only [Call.execute, heapCall, run]
  have bounds : -2 ≤ result.last_flush.toInt ∧ result.last_flush.toInt ≤ 5 := by
    rcases last with eq | eq <;> rw [eq] <;> decide
  exact ⟨used, produced, rc, after, z', result, run,
    ⟨goodA, reachableA, boundary.configuration, Or.inr phaseA, bounds.1, bounds.2⟩, buffersA, account, allowed, ended⟩

end Zlib.Deflate.Engine.Proofs
