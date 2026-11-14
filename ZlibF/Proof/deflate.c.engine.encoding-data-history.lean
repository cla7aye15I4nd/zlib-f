import ZlibF.Proof.«deflate.c.engine.encoding-init-observed»
import ZlibF.Proof.«deflate.c.engine.encoding-finish-observed»
import ZlibF.Spec.Functional.Sequences

/-! # Actual default data histories retain the initialized protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default-entry data epochs without dictionary calls. The caller
may use null or raw output and every signed flush scalar. Constructors
record execution and byte observations, with no assumed invariant or
compression meaning. The public trace below retains exactly the same log.
Other output references and advanced APIs remain outside this refinement. -/
inductive DefaultDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after) →
      DefaultDataTrace r after {}
  | caller {h after log} : DefaultDataTrace r h log → Rebuffer h after r →
      DefaultDataTrace r after log
  | step {h after log z flush rc input output used} : DefaultDataTrace r h log →
      r.get h = some z → (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
      DataStep .deflate h after r flush rc input output used →
      DefaultDataTrace r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END
          boundEligible := log.boundEligible && flush == Z_FINISH }

/-- The scoped history is an actual public data trace, with identical
accepted bytes, emitted bytes, return codes and completion/bound flags.
The default wrapper unfolds to fixed Init2 arguments; no universal Init2
correctness theorem is used. -/
theorem DefaultDataTrace.public_trace {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    DeflateDataTrace Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ _ _ actual ih => exact .step ih actual

/-- This default data epoch never records a dictionary. This is derived
from its actual constructors rather than supplied as an invariant. -/
theorem DefaultDataTrace.dictionary_empty {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : log.dictionary = [] ∧ log.singleDictionary = true := by
  induction history with
  | init => exact ⟨rfl, rfl⟩
  | caller _ _ ih => exact ih
  | step _ _ _ _ ih => exact ih

/-- Every actual successful default init and finite observed history
establishes the same structural protocol. Allocation success is derived
from the init result. Invalid flush scalars and real error returns remain
in the trace and preserve the protocol. Encoding preservation for all
these branches is a separate obligation. -/
theorem DefaultDataTrace.protocol {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config := by
  induction history with
  | init domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      obtain ⟨zf, sf, state⟩ := observed_default_init_encoding_state hf hu hg hz ha hv actual
      exact ⟨_, zf, sf, _, state.protocol⟩
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, boundary⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := boundary.rebuffer edit
      exact ⟨ds, zg, d, config, stateG⟩
  | step _ getZ raw observed ih =>
      obtain ⟨ds, z, d, config, boundary⟩ := ih
      have sameZ : z = _ := Option.some.inj (boundary.good.live.hz.symm.trans getZ)
      subst z
      obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, _input, _used, _output, run⟩ := observed
      have oldEq : oldZ = _ := Option.some.inj (oldGet.symm.trans getZ)
      subst oldZ
      obtain ⟨_used, _produced, _rc, computed, z', result, actual, stateA,
          _buffersA, _account, _allowed⟩ := boundary.all_scalar_request buffers raw _
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      subst computed
      exact ⟨ds, z', result, config, stateA⟩

/-- After any scoped actual observed history, the next signed request
returns with accounting and the preserved protocol. No history or callee
contract is assumed. This structural conclusion does not yet prove the
complete log's functional correctness. -/
theorem DefaultDataTrace.next_request {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config ∧
      ∀ flush, StreamBuffers h r →
        (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
        ∃ used produced rc after z' result,
          deflate (some r) flush h = .ok (rc, after) ∧
          DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
          StreamAccounting z z' used produced ∧
          (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨ds, z, d, config, state⟩ := history.protocol
  exact ⟨ds, z, d, config, state, fun flush buffers raw => state.all_scalar_request buffers raw flush⟩

end Zlib.Deflate.Engine.Proofs
