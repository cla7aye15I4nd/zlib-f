import ZlibF.Proof.«deflate.c.engine.common-initialized-state-init»
import ZlibF.Proof.«deflate.c.engine.common-initialized-request»
import ZlibF.Proof.«deflate.c.engine.encoding-observations»
import ZlibF.Proof.«deflate.c.engine.common-ordinary-history-witness»

/-! # Common-level data histories start directly at actual initialization -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual standard initialization at a normalized slow level, then every
observed NO_FLUSH/FINISH call and legal caller replacement. There is no
positive-first-output premise, engine invariant or callee contract in the
constructors. Initial refusals can therefore precede actual compression. -/
inductive CommonInitializedDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {before after version level p} : InitDomain before r version →
      ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p → 4 ≤ p.level → p.level ≤ 9 →
      C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, after) →
      CommonInitializedDataTrace r after {}
  | caller {h after log} : CommonInitializedDataTrace r h log → Rebuffer h after r →
      CommonInitializedDataTrace r after log
  | step {h after log z flush rc input output used} : CommonInitializedDataTrace r h log →
      r.get h = some z → DeflateCore.Output z.next_out →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      DataStep .deflate h after r flush rc input output used →
      CommonInitializedDataTrace r after (DeflateCore.advanceLog log flush rc input output used)

/-- Observation identity attaches the established encoding theorem to the
exact actual step's returned heap, accepted count and emitted byte list. -/
theorem CommonInitializedEncodingState.ordinary_observed {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    {accepted observed input output : List UInt8} {flush rc : Int32} {used : Nat}
    (state : CommonInitializedEncodingState h r ds z d config accepted observed)
    (raw : DeflateCore.Output z.next_out) (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (step : DataStep .deflate h after r flush rc input output used) :
    ∃ z' result, CommonInitializedEncodingState after r ds z' result config
      (accepted ++ input.take used) (observed ++ output) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ input.take used) (observed ++ output)) := by
  have original := step
  obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _active, snapshot, _used, _bytes, _run⟩ := original
  have same : oldZ = z := Option.some.inj (oldGet.symm.trans state.good.live.hz)
  subst oldZ
  obtain ⟨usedA, rcA, computed, z', result, written, run, stateA, _buffersA, accountA, bytesA, validA⟩ :=
    state.ordinary_encoding_request buffers raw flush flag snapshot
  obtain ⟨heaps, codes, count, bytes⟩ := data_step_identify_actual step state.good.live.hz run stateA.good.live.hz accountA bytesA
  rw [heaps, codes, count, bytes]
  exact ⟨z', result, stateA, validA⟩

/-- The complete observed history invariant starts at real initialization,
including all retries/refusals before the first header output. -/
theorem CommonInitializedDataTrace.encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonInitializedDataTrace r h log) :
    ∃ ds z d config, CommonInitializedEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction history with
  | @init before after version level p domain params low high actual =>
      obtain ⟨zf, sf, state, _initial⟩ := common_observed_initialization_encoding_state domain params low high actual
      refine ⟨before.nextBlk, zf, sf, engineConfig sf, state, ?_⟩
      intro impossible
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, state, valid⟩ := ih
      obtain ⟨zg, _get, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, valid⟩
  | step _ get raw flag observed ih =>
      obtain ⟨ds, z, d, config, state, _valid⟩ := ih
      have same : z = _ := Option.some.inj (state.good.live.hz.symm.trans get)
      subst z
      obtain ⟨z', result, stateA, validA⟩ := state.ordinary_observed raw flag observed
      exact ⟨ds, z', result, config, stateA, validA⟩

/-- At every observed END, all cumulative bytes encode exactly the entire
accepted log, including histories with initial zero-output errors. -/
theorem CommonInitializedDataTrace.completed {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonInitializedDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := history.encoding
  exact valid ended

/-- Earlier positive-first histories retain exactly their actual steps and
log when viewed as histories rooted directly at successful initialization. -/
theorem CommonOrdinaryDataTrace.initialized {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonOrdinaryDataTrace r h log) : CommonInitializedDataTrace r h log := by
  induction history with
  | first domain params low high actual edit get pointer _positive flag observed =>
      exact .step (.caller (.init domain params low high actual) edit) get
        (Or.inr ⟨_, _, pointer⟩) flag observed
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw flag observed ih => exact .step ih get raw flag observed

/-- A real nondefault level-four compression of 300 bytes completes in
this initialized trace. No source input or output observation is changed. -/
theorem common_initialized_level_four_complete_witness :
    ∃ initialized after log,
      C.run (deflateInit_ (some (.tab 0)) (4 : Int32) (.ref (.blk 1) 0) 112) publicWitnessHeap = .ok (Z_OK, initialized) ∧
      CommonInitializedDataTrace (.tab 0) after log ∧ log.input.length = 300 ∧
      log.result = Z_STREAM_END ∧ ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨initialized, after, log, actual, history, count, ended, valid⟩ := common_ordinary_level_four_complete_witness
  exact ⟨initialized, after, log, actual, history.initialized, count, ended, valid⟩

end Zlib.Deflate.Engine.Proofs
