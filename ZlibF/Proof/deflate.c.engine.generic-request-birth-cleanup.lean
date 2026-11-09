import ZlibF.Proof.«deflate.c.engine.generic-request-birth-ownership»
import ZlibF.Proof.«deflate.c.engine.generic-request-trace-cleanup»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- End frees precisely the original five successful-default-init objects after
any all-signed actual request trace and legal caller edits. Every other *current* live
object is retained. Caller edits may change unrelated allocations, so no global
restoration to the pre-init live set is asserted. Normal End retains its actual
BUSY/data-error versus other-status/OK return code. -/
theorem GenericDefaultRequestTrace.birth_cleanup {h : Heap} {r : ZStreamRef} 
    (history : GenericDefaultRequestTrace r h) :
    ∃ before initialized version ds z d config ended,
      InitDomain before r version ∧
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before=.ok (Z_OK,initialized) ∧
      ds=before.nextBlk ∧ initialized.nalloc=before.nalloc+5 ∧
      DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) ∧
      DefaultFinishBoundary h r ds z d config ∧
      (∀ b, DeflateOwned ds d b ↔ before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → h.live b ∧ ¬ before.live b) ∧
      C.run (deflateEnd (some r)) h=.ok ((if d.status=BUSY_STATE then Z_DATA_ERROR else Z_OK),ended) ∧
      r.get ended=some {z with state:=none} ∧
      LiveChange h ended (fun _=>False) (fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, ended.live b ↔ h.live b ∧ ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → ¬ ended.live b) ∧
      (∀ b, ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5) → (ended.live b ↔ h.live b)) ∧
      Frame h ended (fun b=>StreamRoot r b ∨ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      ended.nalloc=h.nalloc ∧ ended.nextBlk=h.nextBlk := by
  obtain ⟨before,initialized,version,ds,z,d,config,domain,actual,key,count,initial,state,owned,birthLive,birthFresh⟩ :=
    history.birth_ownership
  obtain ⟨za,getA,allocators⟩:=history.allocators
  have same : za=z := Option.some.inj (getA.symm.trans state.good.live.hz)
  subst za
  obtain ⟨ended,run,get,live,frame,alloc,next⟩:=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d state.good allocators.2
  have keys : DeflateOwned ds d=(fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) := by
    funext b
    exact propext (owned b)
  rw [keys] at live frame
  have exactLive : ∀ b, ended.live b ↔ h.live b ∧ ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5) := by
    intro b
    simpa only [or_false] using live b
  refine ⟨before,initialized,version,ds,z,d,config,ended,domain,actual,key,count,initial,state,owned,
    fun b lower upper=>⟨birthLive b lower upper,birthFresh b lower upper⟩,
    run,get,live,exactLive,?_,?_,frame,alloc,next⟩
  · intro b lower upper endLive
    exact ((exactLive b).mp endLive).2 ⟨lower,upper⟩
  · intro b outside
    simpa only [outside,not_false_eq_true,and_true] using exactLive b
end Zlib.Deflate.Engine.Proofs
