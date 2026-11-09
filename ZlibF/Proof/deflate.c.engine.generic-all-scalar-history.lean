import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-protocol»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Real initialization and every signed observed call preserve the original
structural boundary for all public caller output views. No UsesFlush restriction,
encoding meaning or representation premise is inserted in the history. -/
theorem GenericDefaultDataTrace.all_scalar_protocol {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
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
  | step _ getZ observed ih =>
      obtain ⟨ds, z, d, config, boundary⟩ := ih
      have sameZ : z = _ := Option.some.inj (boundary.good.live.hz.symm.trans getZ)
      subst z
      obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _header, _input, _used, _output, run⟩ := observed
      have oldEq : oldZ = _ := Option.some.inj (oldGet.symm.trans getZ)
      subst oldZ
      obtain ⟨_used, _produced, _rc, computed, z', result, actual, stateA,
          _buffersA, _account, _allowed⟩ := boundary.generic_all_scalar_request buffers _
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      subst computed
      exact ⟨ds, z', result, config, stateA⟩


/-- Every next signed request returns from the derived all-scalar history boundary. -/
theorem GenericDefaultDataTrace.all_scalar_next_request {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config ∧
      ∀ flush, StreamBuffers h r →
        ∃ used produced rc after z' result,
          deflate (some r) flush h = .ok (rc, after) ∧
          DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
          StreamAccounting z z' used produced ∧
          (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨ds, z, d, config, state⟩ := history.all_scalar_protocol
  exact ⟨ds, z, d, config, state, fun flush buffers => state.generic_all_scalar_request buffers flush⟩

end Zlib.Deflate.Engine.Proofs
