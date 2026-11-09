import ZlibF.Proof.«deflate.c.engine.generic-default-request-trace»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Real basic histories derive the initialized structural protocol at every
step, including repeated input-pointer refusals without readable snapshots. -/
theorem GenericDefaultRequestTrace.protocol {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config := by
  induction history with
  | init domain actual =>
      obtain ⟨fresh,unique,globals,version,z,get,allocators,_null⟩ := domain
      obtain ⟨zf,sf,state⟩ := observed_default_init_encoding_state fresh unique globals get allocators version actual
      exact ⟨_,zf,sf,_,state.protocol⟩
  | caller _ edit ih =>
      obtain ⟨ds,z,d,config,boundary⟩ := ih
      obtain ⟨z',_get',stateA⟩ := boundary.rebuffer edit
      exact ⟨ds,z',d,config,stateA⟩
  | step _ buffers actual ih =>
      obtain ⟨ds,z,d,config,boundary⟩ := ih
      obtain ⟨_used,_produced,_rc,computed,z',result,run,stateA,_buffers,_account,_codes⟩ :=
        boundary.generic_all_scalar_request buffers _
      have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      exact ⟨ds,z',result,config,stateA⟩

/-- Any next signed request is total after every actual basic request history.
Caller buffers are the only next-call premise; no readable snapshot, outputtype,
positive capacity, custom-header or representation premise is introduced. -/
theorem GenericDefaultRequestTrace.next_request {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config ∧
      ∀ flush, StreamBuffers h r →
        ∃ used produced rc after z' result,
          deflate (some r) flush h=.ok (rc,after) ∧
          DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
          StreamAccounting z z' used produced ∧
          (rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR) := by
  obtain ⟨ds,z,d,config,state⟩ := history.protocol
  exact ⟨ds,z,d,config,state,fun flush buffers => state.generic_all_scalar_request buffers flush⟩
end Zlib.Deflate.Engine.Proofs
