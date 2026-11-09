import ZlibF.Proof.«deflate.c.engine.generic-foreign-end-control»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual END determines FINISH and the returned terminal state on every public
output representation and signed request. Entry refusals and new input after
finishing are ruled out by their actual return codes, not caller assumptions. -/
theorem DefaultFinishBoundary.generic_stream_end_run_control
    {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z returned : ZStream} {d result : DeflateState} {config : EngineConfig} {flush : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (actual : deflate (some r) flush h=.ok (Z_STREAM_END,after))
    (goodA : DGood after r ds returned result) :
    flush=Z_FINISH ∧ result.status=FINISH_STATE ∧ returned.avail_in=0 ∧ result.pending=0 ∧ result.bi_valid=0 := by
  have rawControl (raw : z.next_out=.null ∨ ∃ ob oo,z.next_out=.ref (.blk ob) oo) :
      flush=Z_FINISH ∧ result.status=FINISH_STATE ∧ returned.avail_in=0 ∧ result.pending=0 ∧ result.bi_valid=0 := by
    obtain ⟨_used,_written,rc,middle,zm,dm,run,stateA,_buffers,_good,_account,_bytes,_tin,_tout,
      _codes,_error,_bad,terminal,_rest⟩:=boundary.all_scalar_request_contract flush buffers raw
    obtain ⟨code,heap⟩:=Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    subst rc middle
    have streams : zm=returned:=Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
    have states : dm=result:=Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
    subst zm dm
    exact terminal rfl
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact rawControl (Or.inl null)
  · exact rawControl (Or.inr raw)
  · by_cases finish : flush=Z_FINISH
    · subst flush
      exact ⟨rfl,boundary.generic_foreign_finish_end_run_control buffers pointer actual goodA⟩
    · exfalso
      by_cases noFlush : flush=Z_NO_FLUSH
      · subst flush
        obtain ⟨_used,_produced,rc,_middle,_zm,_dm,run,_state,_buffers,_account,codes⟩ :=
          boundary.foreign_no_flush_total buffers pointer
        have code : rc=Z_STREAM_END:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
        have noEnd : rc≠Z_STREAM_END := by rcases codes with rfl|rfl|rfl <;> decide
        exact noEnd code
      · by_cases part : flush=Z_PARTIAL_FLUSH
        · obtain ⟨_used,_produced,rc,_middle,_zm,_dm,run,_state,_buffers,_account,codes⟩ :=
            boundary.foreign_partial_total buffers (Or.inr ⟨owner,oo,pointer⟩) flush part
          have code : rc=Z_STREAM_END:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
          have noEnd : rc≠Z_STREAM_END := by rcases codes with rfl|rfl|rfl <;> decide
          exact noEnd code
        · by_cases marker : flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK
          · obtain ⟨_used,_produced,rc,_middle,_zm,_dm,run,_state,_buffers,_account,codes⟩ :=
              boundary.foreign_sync_full_block_total buffers (Or.inr ⟨owner,oo,pointer⟩) flush marker
            have code : rc=Z_STREAM_END:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
            have noEnd : rc≠Z_STREAM_END := by rcases codes with rfl|rfl|rfl <;> decide
            exact noEnd code
          · have bad : flush > Z_BLOCK ∨ flush < 0 := by
              have n0 : flush.toInt≠0 := fun eq=>noFlush (Int32.toInt_inj.mp eq)
              have n1 : flush.toInt≠1 := fun eq=>part (Int32.toInt_inj.mp eq)
              have n2 : flush.toInt≠2 := fun eq=>marker (Or.inl (Int32.toInt_inj.mp eq))
              have n3 : flush.toInt≠3 := fun eq=>marker (Or.inr (Or.inl (Int32.toInt_inj.mp eq)))
              have n4 : flush.toInt≠4 := fun eq=>finish (Int32.toInt_inj.mp eq)
              have n5 : flush.toInt≠5 := fun eq=>marker (Or.inr (Or.inr (Int32.toInt_inj.mp eq)))
              have outside : flush.toInt<0 ∨ 5<flush.toInt := by omega
              exact outside.elim (fun low=>Or.inr (Int32.lt_iff_toInt_lt.mpr low))
                (fun high=>Or.inl (Int32.lt_iff_toInt_lt.mpr high))
            have run:=public_bad_flush_refusal boundary.good flush bad
            have code : Z_STREAM_ERROR=Z_STREAM_END:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
            exact (by decide : Z_STREAM_ERROR≠Z_STREAM_END) code
end Zlib.Deflate.Engine.Proofs
