import ZlibF.Proof.«deflate.c.engine.generic-ordinary-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-default-data-trace»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed request returns on every caller output view allowed by the
original public buffers. All six valid flags, invalid-scalar refusals, zero
capacity, input guards, pending output and finished-state refusals are actual.
This structural protocol result adds no encoding or callee-contract premise. -/
theorem DefaultFinishBoundary.generic_all_scalar_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR) := by
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact boundary.all_scalar_request buffers (Or.inl null) flush
  · exact boundary.all_scalar_request buffers (Or.inr raw) flush
  · by_cases ordinary : flush=Z_NO_FLUSH ∨ flush=Z_FINISH
    · exact boundary.generic_ordinary_request flush ordinary buffers
    · by_cases part : flush=Z_PARTIAL_FLUSH
      · obtain ⟨used,produced,rc,after,z',result,run,stateA,buffersA,account,codes⟩ :=
          boundary.foreign_partial_total buffers (Or.inr ⟨owner,oo,pointer⟩) flush part
        exact ⟨used,produced,rc,after,z',result,run,stateA,buffersA,account,
          codes.elim Or.inl (fun code => Or.inr (Or.inr code))⟩
      · by_cases marker : flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK
        · obtain ⟨used,produced,rc,after,z',result,run,stateA,buffersA,account,codes⟩ :=
            boundary.foreign_sync_full_block_total buffers (Or.inr ⟨owner,oo,pointer⟩) flush marker
          exact ⟨used,produced,rc,after,z',result,run,stateA,buffersA,account,
            codes.elim Or.inl (fun code => Or.inr (Or.inr code))⟩
        · have bad : flush > Z_BLOCK ∨ flush < 0 := by
            have n0 : flush.toInt≠0 := fun eq => ordinary (Or.inl (Int32.toInt_inj.mp eq))
            have n1 : flush.toInt≠1 := fun eq => part (Int32.toInt_inj.mp eq)
            have n2 : flush.toInt≠2 := fun eq => marker (Or.inl (Int32.toInt_inj.mp eq))
            have n3 : flush.toInt≠3 := fun eq => marker (Or.inr (Or.inl (Int32.toInt_inj.mp eq)))
            have n4 : flush.toInt≠4 := fun eq => ordinary (Or.inr (Int32.toInt_inj.mp eq))
            have n5 : flush.toInt≠5 := fun eq => marker (Or.inr (Or.inr (Int32.toInt_inj.mp eq)))
            have outside : flush.toInt<0 ∨ 5<flush.toInt := by omega
            exact outside.elim (fun low => Or.inr (Int32.lt_iff_toInt_lt.mpr low))
              (fun high => Or.inl (Int32.lt_iff_toInt_lt.mpr high))
          exact ⟨0,0,Z_STREAM_ERROR,h,z,d,public_bad_flush_refusal boundary.good flush bad,
            boundary,buffers,stream_accounting_zero z,Or.inr (Or.inr (Or.inl rfl))⟩

end Zlib.Deflate.Engine.Proofs
