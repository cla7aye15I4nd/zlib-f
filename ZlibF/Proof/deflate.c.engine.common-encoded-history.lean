import ZlibF.Proof.«deflate.c.engine.common-encoded-initial»
import ZlibF.Proof.«deflate.c.engine.common-encoded-request»
import ZlibF.Proof.«deflate.c.engine.encoding-observations»
import ZlibF.Proof.«public-deflate-end»
import ZlibF.Spec.Public.DeflateCore

/-! # Actual initialized common-level NO_FLUSH/FINISH histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Scope: standard initializer with normalized level four through nine;
first caller output capacity one, then null/raw output and NO_FLUSH or
FINISH. Constructors record actual executions and byte observations only.
No engine, encoding or callee-contract premise is part of this history. -/
inductive CommonDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | first {before initialized h after version level p z ob oo flush rc input output used} :
      InitDomain before r version →
      ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p → 4 ≤ p.level → p.level ≤ 9 →
      C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized) →
      Rebuffer initialized h r → r.get h = some z →
      z.next_out = .ref (.blk ob) oo → z.avail_out = 1 →
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      DataStep .deflate h after r flush rc input output used →
      CommonDataTrace r after (DeflateCore.advanceLog {} flush rc input output used)
  | caller {h after log} : CommonDataTrace r h log → Rebuffer h after r → CommonDataTrace r after log
  | step {h after log z flush rc input output used} : CommonDataTrace r h log →
      r.get h = some z → DeflateCore.Output z.next_out →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      DataStep .deflate h after r flush rc input output used →
      CommonDataTrace r after (DeflateCore.advanceLog log flush rc input output used)


/-- A real observed ordinary step identifies the proved returned heap,
accepted count and emitted bytes, without a semantic history assumption. -/
theorem CommonEncodingState.ordinary_observed {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    {accepted observed input output : List UInt8} {flush rc : Int32} {used : Nat}
    (state : CommonEncodingState h r ds z d config accepted observed)
    (raw : DeflateCore.Output z.next_out) (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (step : DataStep .deflate h after r flush rc input output used) :
    ∃ z' result, CommonEncodingState after r ds z' result config
      (accepted ++ input.take used) (observed ++ output) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted ++ input.take used) (observed ++ output)) := by
  have original := step
  obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, snapshot, _used, _bytes, _run⟩ := original
  have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
  subst oldZ
  obtain ⟨usedA, rcA, computed, z', result, written, run, stateA, _buffersA, accountA, bytesA, validA⟩ :=
    state.ordinary_encoding_request buffers raw flush flag snapshot
  obtain ⟨heaps, codes, count, bytes⟩ := data_step_identify_actual step state.protocol.good.live.hz run
    stateA.protocol.good.live.hz accountA bytesA
  rw [heaps, codes, count, bytes]
  exact ⟨z', result, stateA, validA⟩

/-- Every actual scoped history retains the cumulative observed input and
output meaning. A completed call establishes validity for precisely the
observed stream, including errors and caller output reuse along the way. -/
theorem CommonDataTrace.encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) :
    ∃ ds z d config, CommonEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction history with
  | @first before initialized h after version level p z ob oo flush rc input output used
      domain params low high actual edit get pointer one flagLow flagHigh observed =>
      obtain ⟨zf, sf, _start, _initial, first⟩ := common_observed_initialization_encoding domain params low high actual
      obtain ⟨zg, getG, next⟩ := first h edit
      have same : zg = z := Option.some.inj (getG.symm.trans get)
      subst zg
      have original := observed
      obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, snapshot, _used, _bytes, _run⟩ := original
      have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans get)
      subst oldZ
      have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := by
        intro nonempty null
        rw [null] at snapshot
        rcases snapshot with ⟨_, zero, _⟩ | ⟨_, _, _, impossible, _⟩
        · exact nonempty (UInt32.toNat_inj.mp zero)
        · cases impossible
      obtain ⟨computed, z', result, run, stateA, _buffersA, accountA, bytesA⟩ :=
        next ob oo pointer one buffers valid flush flagLow flagHigh
      have account : StreamAccounting z z' 0 ([120] : List UInt8).length := accountA
      obtain ⟨heaps, codes, count, written⟩ := data_step_identify_actual observed get run
        stateA.protocol.good.live.hz account bytesA
      rw [heaps, codes, count, written]
      refine ⟨before.nextBlk, z', result, engineConfig sf, ?_, ?_⟩
      · simpa only [DeflateCore.advanceLog, List.take_zero, List.append_nil, List.nil_append] using stateA
      · intro impossible
        exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, state, ended⟩ := ih
      obtain ⟨zg, _get, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, ended⟩
  | step _ get raw flag observed ih =>
      obtain ⟨ds, current, d, config, state, _ended⟩ := ih
      have same : current = _ := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
      subst current
      obtain ⟨z', result, stateA, validA⟩ := state.ordinary_observed raw flag observed
      exact ⟨ds, z', result, config, stateA, validA⟩

/-- Every observed END encodes the entire accepted log. No caller-supplied
semantic encoding premise is required. -/
theorem CommonDataTrace.completed {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := history.encoding
  exact valid ended

end Zlib.Deflate.Engine.Proofs
