import ZlibF.Proof.«deflate.c.engine.generic-foreign-error-iff»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact STREAM_ERROR classification for every signed request and every output
representation allowed by the public buffers. Zero output and finished-state new
input are classified by the actual source and remain in the original domain. -/
theorem DefaultFinishBoundary.generic_stream_error_run_iff
    {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (actual : deflate (some r) flush h=.ok (rc,after)) :
    (rc=Z_STREAM_ERROR ↔ flush.toInt<0 ∨ 5<flush.toInt ∨ z.next_out=.null ∨
      (z.next_in=.null ∧ z.avail_in≠0) ∨ (d.status=FINISH_STATE ∧ flush≠Z_FINISH)) := by
  have rawControl (raw : z.next_out=.null ∨ ∃ ob oo,z.next_out=.ref (.blk ob) oo) :
      rc=Z_STREAM_ERROR ↔ flush.toInt<0 ∨ 5<flush.toInt ∨ z.next_out=.null ∨
        (z.next_in=.null ∧ z.avail_in≠0) ∨ (d.status=FINISH_STATE ∧ flush≠Z_FINISH) := by
    obtain ⟨_used,_written,ret,_middle,_zm,_dm,run,_state,_buffers,_good,_account,_bytes,_tin,_tout,
      _codes,errors,_rest⟩:=boundary.all_scalar_request_contract flush buffers raw
    have code : ret=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
    simpa only [code] using errors
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact rawControl (Or.inl null)
  · exact rawControl (Or.inr raw)
  · exact boundary.generic_foreign_stream_error_run_iff buffers pointer actual

/-- An out-of-range signed flag returns STREAM_ERROR on the identical heap.
No buffers, readable input, output shape or capacity premise is needed. -/
theorem DefaultFinishBoundary.generic_bad_scalar_run_control
    {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (actual : deflate (some r) flush h=.ok (rc,after))
    (bad : flush.toInt<0 ∨ 5<flush.toInt) : rc=Z_STREAM_ERROR ∧ after=h := by
  have badSource : flush>Z_BLOCK ∨ flush<0 := by
    exact bad.elim (fun low=>Or.inr (Int32.lt_iff_toInt_lt.mpr low))
      (fun high=>Or.inl (Int32.lt_iff_toInt_lt.mpr high))
  have run:=public_bad_flush_refusal boundary.good flush badSource
  obtain ⟨code,heap⟩:=Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  exact ⟨code.symm,heap.symm⟩
end Zlib.Deflate.Engine.Proofs
