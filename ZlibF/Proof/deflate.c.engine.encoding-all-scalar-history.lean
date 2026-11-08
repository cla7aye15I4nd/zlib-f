import ZlibF.Proof.«deflate.c.engine.encoding-data-history»
import ZlibF.Proof.«deflate.c.engine.encoded-state-scalar-request»

/-! # Every actual signed request history retains exact independent encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual observed DataStep advances exactly its recorded input
prefix and emitted bytes for any signed flush parameter. Observation
identity follows from the actual run and proved accounting, with no
encoding or accounting premise added to DataStep. -/
theorem DefaultEncodingState.scalar_observed {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    {accepted observed actualInput actualOutput : List UInt8} {flush rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (step : DataStep .deflate h after r flush rc actualInput actualOutput used) :
    ∃ z' result, DefaultEncodingState after r ds z' result config
      (accepted ++ actualInput.take used) (observed ++ actualOutput) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ actualOutput)) := by
  have originalStep := step
  obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, snapshot, _usedEq, _bytes, _run⟩ := originalStep
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
  subst oldZ
  obtain ⟨acceptedCount, ret, computed, z', result, written, run, stateA, _buffersA, accountA, bytesA, endedA⟩ :=
    state.scalar_encoding_request buffers raw flush snapshot
  obtain ⟨heaps, code, counts, writtenEq⟩ := data_step_identify_actual step state.protocol.good.live.hz run
    stateA.protocol.good.live.hz accountA bytesA
  rw [heaps, code, counts, writtenEq]
  exact ⟨z', result, stateA, endedA⟩

/-- Actual successful default init, every finite signed request schedule
and legal caller rebuffering retain encoding of the same observed bytes.
All six valid flags, invalid scalar refusals, duplicates, partial headers,
pending output and finished-state calls are included. A latest STREAM_END
result gives independent zlib validity for exactly the observed accepted
input and cumulative output. No schedule or representation premise is
added to the actual trace. Scope is the explicit DefaultDataTrace domain:
default parameters, null/raw output, no dictionary/advanced operations.
Bound-based completion and the unchanged full public targets remain open. -/
theorem DefaultDataTrace.encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction history with
  | init domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      obtain ⟨zf, sf, state⟩ := observed_default_init_encoding_state hf hu hg hz ha hv actual
      refine ⟨_, zf, sf, engineConfig sf, state, ?_⟩
      intro impossible
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, state, ended⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, ended⟩
  | step _ getZ raw observed ih =>
      obtain ⟨ds, oldZ, d, config, state, _previousEnd⟩ := ih
      have sameZ : oldZ = _ := Option.some.inj (state.protocol.good.live.hz.symm.trans getZ)
      subst oldZ
      obtain ⟨z', result, stateA, endedA⟩ := state.scalar_observed raw observed
      exact ⟨ds, z', result, config, stateA, endedA⟩

/-- Every completed scoped actual default data trace has the public
sequence's exact DecodesFor conclusion, for every flush schedule and the
unchanged observed log. There is no UsesFlush restriction. This supporting
refinement does not register the full sequence or completion target. -/
theorem DefaultDataTrace.decodes {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    DecodesFor (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) log.dictionary log.output log.input := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := history.encoding
  change ZlibF.Spec.Zlib.Decodes log.dictionary log.output log.input
  rw [history.dictionary_empty.1]
  exact valid ended

end Zlib.Deflate.Engine.Proofs
