import ZlibF.Proof.«deflate.c.engine.generic-stream-end-control»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- From one real END request, derive terminal status and then run real End.
The same returned heap is used for exact original-birth release. No final-status,
accepted-input, output-representation or readable-snapshot premise is added. -/
theorem GenericDefaultRequestTrace.completed_birth_cleanup
    {h after : Heap} {r : ZStreamRef} {flush : Int32}
    (history : GenericDefaultRequestTrace r h) (buffers : StreamBuffers h r)
    (actual : deflate (some r) flush h=.ok (Z_STREAM_END,after)) :
    ∃ before initialized version ds z d config ended,
      InitDomain before r version ∧
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before=.ok (Z_OK,initialized) ∧
      ds=before.nextBlk ∧ initialized.nalloc=before.nalloc+5 ∧
      DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) ∧
      DefaultFinishBoundary after r ds z d config ∧
      flush=Z_FINISH ∧ d.status=FINISH_STATE ∧ z.avail_in=0 ∧ d.pending=0 ∧ d.bi_valid=0 ∧
      (∀ b, DeflateOwned ds d b ↔ before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → after.live b ∧ ¬ before.live b) ∧
      C.run (deflateEnd (some r)) after=.ok (Z_OK,ended) ∧
      r.get ended=some {z with state:=none} ∧
      LiveChange after ended (fun _=>False) (fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, ended.live b ↔ after.live b ∧ ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → ¬ ended.live b) ∧
      (∀ b, ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5) → (ended.live b ↔ after.live b)) ∧
      Frame after ended (fun b=>StreamRoot r b ∨ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      ended.nalloc=after.nalloc ∧ ended.nextBlk=after.nextBlk := by
  obtain ⟨oldDs,oldZ,oldD,oldConfig,boundary⟩:=history.protocol
  obtain ⟨_used,_produced,rc,computed,returned,result,run,stateA,_buffers,_account,_codes⟩:=
    boundary.generic_all_scalar_request buffers flush
  obtain ⟨code,heap⟩:=Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  subst rc computed
  have terminal:=boundary.generic_stream_end_run_control buffers actual stateA.good
  have historyA : GenericDefaultRequestTrace r after:=.step history buffers actual
  obtain ⟨before,initialized,version,ds,z,d,config,ended,domain,initRun,key,count,initial,
    state,owned,fresh,cleanup,get,live,exactLive,freed,others,frame,nalloc,next⟩:=historyA.birth_cleanup
  have streams : z=returned:=Option.some.inj (state.good.live.hz.symm.trans stateA.good.live.hz)
  subst z
  have keys : ds=oldDs := by
    injection state.good.live.zst.symm.trans stateA.good.live.zst with tagged
    injection tagged
  rw [keys] at state owned key
  have states : d=result:=Option.some.inj (state.good.live.hs.symm.trans stateA.good.live.hs)
  subst d
  have notBusy : result.status≠BUSY_STATE := by
    rw [terminal.2.1]
    decide
  rw [ite_eq_right notBusy] at cleanup
  exact ⟨before,initialized,version,oldDs,returned,result,config,ended,domain,initRun,key,count,
    initial,state,terminal.1,terminal.2.1,terminal.2.2.1,terminal.2.2.2.1,terminal.2.2.2.2,
    owned,fresh,cleanup,get,live,exactLive,freed,others,frame,nalloc,next⟩
end Zlib.Deflate.Engine.Proofs
