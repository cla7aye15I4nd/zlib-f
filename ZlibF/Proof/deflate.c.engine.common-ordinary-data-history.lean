import ZlibF.Proof.«deflate.c.engine.common-encoded-history»
import ZlibF.Proof.«deflate.c.engine.common-initial-first-ordinary-encoding»
import ZlibF.Proof.«deflate.c.engine.common-encoded-request»
import ZlibF.Proof.«deflate.c.engine.encoding-observations»
import ZlibF.Proof.«public-deflate-end»
import ZlibF.Spec.Public.DeflateCore
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

/-! # Actual initialized common-level NO_FLUSH/FINISH histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Scope: standard initializer with normalized level four through nine;
first NO_FLUSH or FINISH with any positive raw output capacity, then null/raw
output and NO_FLUSH or FINISH. Constructors record actual executions and byte observations only.
No engine, encoding or callee-contract premise is part of this history. -/
inductive CommonOrdinaryDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | first {before initialized h after version level p z ob oo flush rc input output used} :
      InitDomain before r version →
      ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p → 4 ≤ p.level → p.level ≤ 9 →
      C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized) →
      Rebuffer initialized h r → r.get h = some z →
      z.next_out = .ref (.blk ob) oo → 0 < z.avail_out.toNat →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      DataStep .deflate h after r flush rc input output used →
      CommonOrdinaryDataTrace r after (DeflateCore.advanceLog {} flush rc input output used)
  | caller {h after log} : CommonOrdinaryDataTrace r h log → Rebuffer h after r → CommonOrdinaryDataTrace r after log
  | step {h after log z flush rc input output used} : CommonOrdinaryDataTrace r h log →
      r.get h = some z → DeflateCore.Output z.next_out →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      DataStep .deflate h after r flush rc input output used →
      CommonOrdinaryDataTrace r after (DeflateCore.advanceLog log flush rc input output used)


/-- Every actual scoped history retains the cumulative observed input and
output meaning. A completed call establishes validity for precisely the
observed stream, including errors and caller output reuse along the way. -/
theorem CommonOrdinaryDataTrace.encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonOrdinaryDataTrace r h log) :
    ∃ ds z d config, CommonEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction history with
  | @first before initialized h after version level p z ob oo flush rc input output used
      domain params low high actual edit get pointer positive firstFlag observed =>
      obtain ⟨zf, sf, _start, _initial, first⟩ := common_observed_initialization_first_ordinary_encoding domain params low high actual
      obtain ⟨zg, getG, next⟩ := first h edit
      have same : zg = z := Option.some.inj (getG.symm.trans get)
      subst zg
      have original := observed
      obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, snapshot, _used, _bytes, _run⟩ := original
      have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans get)
      subst oldZ
      obtain ⟨actualUsed, actualRC, computed, z', result, actualWritten, run, stateA, _buffersA, accountA, bytesA, _codes, endedA⟩ :=
        next ob oo pointer positive buffers input snapshot flush firstFlag
      obtain ⟨heaps, codes, count, written⟩ := data_step_identify_actual observed get run
        stateA.protocol.good.live.hz accountA bytesA
      rw [heaps, codes, count, written]
      refine ⟨before.nextBlk, z', result, engineConfig sf, ?_, ?_⟩
      · simpa only [DeflateCore.advanceLog, List.nil_append] using stateA
      · simpa only [DeflateCore.advanceLog, List.nil_append] using endedA
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
theorem CommonOrdinaryDataTrace.completed {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonOrdinaryDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    ZlibF.Spec.Zlib.Valid log.input log.output := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := history.encoding
  exact valid ended

end Zlib.Deflate.Engine.Proofs
