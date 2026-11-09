import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-no-error»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact STREAM_ERROR classification for actual foreign-depth caller output.
Zero capacity, duplicate requests and new input after finishing remain in the
domain and use their actual non-STREAM_ERROR returns where appropriate. -/
theorem DefaultFinishBoundary.generic_foreign_stream_error_run_iff
    {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (actual : deflate (some r) flush h=.ok (rc,after)) :
    (rc=Z_STREAM_ERROR ↔ flush.toInt<0 ∨ 5<flush.toInt ∨ z.next_out=.null ∨
      (z.next_in=.null ∧ z.avail_in≠0) ∨ (d.status=FINISH_STATE ∧ flush≠Z_FINISH)) := by
  by_cases bad : flush.toInt<0 ∨ 5<flush.toInt
  · have badSource : flush>Z_BLOCK ∨ flush<0 := by
      exact bad.elim (fun low=>Or.inr (Int32.lt_iff_toInt_lt.mpr low))
        (fun high=>Or.inl (Int32.lt_iff_toInt_lt.mpr high))
    have run:=public_bad_flush_refusal boundary.good flush badSource
    have code : Z_STREAM_ERROR=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
    exact ⟨fun _=>bad.elim Or.inl (fun high=>Or.inr (Or.inl high)),fun _=>code.symm⟩
  · have lower : 0≤flush.toInt := by omega
    have upper : flush.toInt≤Z_BLOCK.toInt := by change flush.toInt≤5;omega
    by_cases guard : z.next_out=.null ∨ (z.next_in=.null ∧ z.avail_in≠0) ∨
        (d.status=FINISH_STATE ∧ flush≠Z_FINISH)
    · have sourceGuard : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
          (d.status=FINISH_STATE ∧ flush≠Z_FINISH) := by simpa only [and_comm] using guard
      have source:=public_stream_guard_refusal boundary.good flush lower upper sourceGuard
      obtain ⟨_message,refused⟩:=err_return_run boundary.good.live.hz Z_STREAM_ERROR
      have code : Z_STREAM_ERROR=rc:=(Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans actual))).1
      exact ⟨fun _=>Or.inr (Or.inr guard),fun _=>code.symm⟩
    · have nonnull : z.next_out≠.null := fun eq=>guard (Or.inl eq)
      have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq=>guard (Or.inr (Or.inl ⟨eq,count⟩))
      have finishAllowed : d.status=FINISH_STATE → flush=Z_FINISH := by
        intro status
        by_cases finish : flush=Z_FINISH
        · exact finish
        · exact False.elim (guard (Or.inr (Or.inr ⟨status,finish⟩)))
      have noError : rc≠Z_STREAM_ERROR := by
        by_cases zero : z.avail_out=0
        · have source:=public_zero_output_refusal boundary.good flush lower upper nonnull valid finishAllowed zero
          obtain ⟨_message,refused⟩:=err_return_run boundary.good.live.hz Z_BUF_ERROR
          have code : Z_BUF_ERROR=rc:=(Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans actual))).1
          rw [←code]
          decide
        · have positive : 0<z.avail_out.toNat := by
            have nonzero : z.avail_out.toNat≠0 := fun eq=>zero (UInt32.toNat_inj.mp eq)
            omega
          by_cases part : flush=Z_PARTIAL_FLUSH
          · have active : d.status≠FINISH_STATE := by
              intro status
              have impossible:=finishAllowed status
              rw [part] at impossible
              exact (by decide : Z_PARTIAL_FLUSH≠Z_FINISH) impossible
            obtain ⟨_used,_produced,ret,_middle,_zm,_dm,run,_state,_buffers,_account,codes⟩:=
              boundary.foreign_partial_active buffers pointer positive valid active flush part
            have code : ret=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
            rw [code] at codes
            rcases codes with rfl|rfl <;> decide
          · by_cases marker : flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK
            · have nonfinal : flush≠Z_FINISH := by rcases marker with rfl|rfl|rfl <;> decide
              have active : d.status≠FINISH_STATE := fun status=>nonfinal (finishAllowed status)
              obtain ⟨_used,_produced,ret,_middle,_zm,_dm,run,_state,_buffers,_account,codes⟩:=
                boundary.foreign_sync_full_block_active buffers pointer positive valid active flush marker
              have code : ret=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
              rw [code] at codes
              rcases codes with rfl|rfl <;> decide
            · have ordinary : flush=Z_NO_FLUSH ∨ flush=Z_FINISH := by
                have n1 : flush.toInt≠1 := fun eq=>part (Int32.toInt_inj.mp eq)
                have n2 : flush.toInt≠2 := fun eq=>marker (Or.inl (Int32.toInt_inj.mp eq))
                have n3 : flush.toInt≠3 := fun eq=>marker (Or.inr (Or.inl (Int32.toInt_inj.mp eq)))
                have n5 : flush.toInt≠5 := fun eq=>marker (Or.inr (Or.inr (Int32.toInt_inj.mp eq)))
                have possible : flush.toInt=0 ∨ flush.toInt=4 := by change flush.toInt≤5 at upper;omega
                exact possible.elim (fun eq=>Or.inl (Int32.toInt_inj.mp eq)) (fun eq=>Or.inr (Int32.toInt_inj.mp eq))
              exact boundary.generic_foreign_ordinary_no_error buffers pointer ordinary positive valid finishAllowed actual
      refine ⟨fun err=>False.elim (noError err),?_⟩
      intro impossible
      rcases impossible with low|high|out|input|finish
      · exact False.elim (bad (Or.inl low))
      · exact False.elim (bad (Or.inr high))
      · exact False.elim (guard (Or.inl out))
      · exact False.elim (guard (Or.inr (Or.inl input)))
      · exact False.elim (guard (Or.inr (Or.inr finish)))
end Zlib.Deflate.Engine.Proofs
