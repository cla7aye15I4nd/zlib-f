import ZlibF.Proof.«deflate.c.engine.encoding-data-history»
import ZlibF.Proof.«deflate.c.engine.encoded-state-ordinary-request»

/-! # Ordinary observed histories carry exact independent compression meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual ordinary DataStep advances exactly its recorded consumed
prefix and output bytes. Actual run determinism identifies both counts
and byte lists with the execution proof. Error returns are included. -/
theorem DefaultEncodingState.ordinary_observed {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    {accepted observed actualInput actualOutput : List UInt8} {flush rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (step : DataStep .deflate h after r flush rc actualInput actualOutput used) :
    ∃ z' result, DefaultEncodingState after r ds z' result config
      (accepted ++ actualInput.take used) (observed ++ actualOutput) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ actualInput.take used) (observed ++ actualOutput)) := by
  have originalStep := step
  obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, snapshot, _usedEq, _bytes, _run⟩ := originalStep
  have oldEq : oldZ = z := Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
  subst oldZ
  obtain ⟨acceptedCount, ret, computed, z', result, written, run, stateA, _buffersA, accountA, bytesA, endedA⟩ :=
    state.ordinary_encoding_request buffers raw flush flag snapshot
  obtain ⟨heaps, code, counts, writtenEq⟩ := data_step_identify_actual step state.protocol.good.live.hz run
    stateA.protocol.good.live.hz accountA bytesA
  rw [heaps, code, counts, writtenEq]
  exact ⟨z', result, stateA, endedA⟩

/-- A schedule property of an actual data trace. It changes no caller
domain, event, observation or return code and assumes no representation
invariant. The full trace admits all signed flags; this property selects
which per-flag encoding transition is available to an induction. -/
inductive DefaultDataTrace.UsesFlush {r : ZStreamRef} (allowed : Int32 → Prop) :
    {h : Heap} → {log : DataLog} → DefaultDataTrace r h log → Prop
  | init {h after version} {domain : InitDomain h r version}
      {actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)} :
      UsesFlush allowed (.init domain actual)
  | caller {h after log} {history : DefaultDataTrace r h log} {edit : Rebuffer h after r} :
      UsesFlush allowed history → UsesFlush allowed (.caller history edit)
  | step {h after log z flush rc input output used} {history : DefaultDataTrace r h log}
      {getZ : r.get h = some z} {raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo}
      {observed : DataStep .deflate h after r flush rc input output used} :
      UsesFlush allowed history → allowed flush → UsesFlush allowed (.step history getZ raw observed)

/-- Actual default initialization, arbitrary finite NO_FLUSH/FINISH data
schedules and legal caller rebuffering establish exact encoding for the
same observed input/output. No step requires successful compression:
zero/null-output errors, duplicate refusals, finished-state new input and
wrong-flush refusals remain included. END implies independent zlib
validity. BLOCK/PARTIAL/SYNC/FULL encoding, the bound completion theorem
and advanced APIs remain obligations of the full public sequence target. -/
theorem DefaultDataTrace.ordinary_encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    {history : DefaultDataTrace r h log}
    (flags : history.UsesFlush (fun flush => flush = Z_NO_FLUSH ∨ flush = Z_FINISH)) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction flags with
  | @init h after version domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      obtain ⟨zf, sf, state⟩ := observed_default_init_encoding_state hf hu hg hz ha hv actual
      refine ⟨h.nextBlk, zf, sf, engineConfig sf, state, ?_⟩
      intro impossible
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)
  | @caller h after log history edit _flags ih =>
      obtain ⟨ds, z, d, config, state, ended⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, ended⟩
  | @step h after log z flush rc input output used history getZ raw observed _flags flag ih =>
      obtain ⟨ds, oldZ, d, config, state, _previousEnd⟩ := ih
      have sameZ : oldZ = z := Option.some.inj (state.protocol.good.live.hz.symm.trans getZ)
      subst oldZ
      obtain ⟨z', result, stateA, endedA⟩ := state.ordinary_observed raw flag observed
      exact ⟨ds, z', result, config, stateA, endedA⟩

/-- The ordinary-history result has exactly the public sequence's
DecodesFor conclusion at default parameters, for the actual unchanged log.
This is a scoped refinement, not registration of the full sequence goal. -/
theorem DefaultDataTrace.ordinary_decodes {h : Heap} {r : ZStreamRef} {log : DataLog}
    {history : DefaultDataTrace r h log}
    (flags : history.UsesFlush (fun flush => flush = Z_NO_FLUSH ∨ flush = Z_FINISH))
    (ended : log.result = Z_STREAM_END) :
    DecodesFor (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) log.dictionary log.output log.input := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := ordinary_encoding flags
  change ZlibF.Spec.Zlib.Decodes log.dictionary log.output log.input
  rw [history.dictionary_empty.1]
  exact valid ended

end Zlib.Deflate.Engine.Proofs
