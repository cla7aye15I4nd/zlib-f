import ZlibF.Proof.«deflate.c.engine.generic-request-trace-protocol»
import ZlibF.Proof.«deflate.c.engine.observed-history-contract»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual initialization and every basic request, including unreadable-input
refusals, retain the default allocator identities. No snapshot is needed. -/
theorem GenericDefaultRequestTrace.allocators {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) : ∃ z, r.get h=some z ∧ DefAlloc z := by
  induction history with
  | init domain actual => exact (DefaultDataTrace.init domain actual).allocators
  | caller _ edit ih =>
      obtain ⟨z,getZ,allocators⟩ := ih
      obtain ⟨_fresh,_unique,_globals,_frame,old,next,getOld,getNext,fields⟩ := edit
      have same : old=z := Option.some.inj (getOld.symm.trans getZ)
      subst old
      refine ⟨next,getNext,?_⟩
      rw [fields]
      exact allocators
  | step previous buffers actual ih =>
      obtain ⟨old,getOld,allocators⟩ := ih
      obtain ⟨ds,z,d,config,state⟩ := previous.protocol
      have same : old=z := Option.some.inj (getOld.symm.trans state.good.live.hz)
      subst old
      obtain ⟨_used,_produced,_rc,computed,z',result,run,stateA,_buffers,account,_codes⟩ :=
        state.generic_all_scalar_request buffers _
      have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      rcases account with ⟨_,_,_,_,_,_,_,alloc,free,_,_⟩
      exact ⟨z',stateA.good.live.hz,alloc.trans allocators.1,free.trans allocators.2⟩

/-- End is a real no-fault call releasing exactly the current five owned objects
for every basic request history. This includes errors and unreadable-input refusals.
A separate original-birth ledger identifies those five with init's original IDs. -/
theorem GenericDefaultRequestTrace.cleanup {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) :
    ∃ ds z d after, DGood h r ds z d ∧
      C.run (deflateEnd (some r)) h=.ok ((if d.status=BUSY_STATE then Z_DATA_ERROR else Z_OK),after) ∧
      r.get after=some {z with state:=none} ∧
      LiveChange h after (fun _ =>False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  obtain ⟨ds,z,d,config,state⟩ := history.protocol
  obtain ⟨allocated,getAllocated,allocators⟩ := history.allocators
  have same : allocated=z := Option.some.inj (getAllocated.symm.trans state.good.live.hz)
  subst allocated
  obtain ⟨after,run,get,live,frame,count,next⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d state.good allocators.2
  exact ⟨ds,z,d,after,state.good,run,get,live,frame,count,next⟩
end Zlib.Deflate.Engine.Proofs
