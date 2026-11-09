import ZlibF.Proof.«deflate.c.engine.generic-initial-birth»
import ZlibF.Proof.«deflate.c.engine.generic-default-request-trace»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Real default init births exactly five objects. Caller edits and every signed
actual call retain their same four owning pointers and live state key. No
representation or ownership contract is an additional trace constructor premise. -/
theorem GenericDefaultRequestTrace.birth_ownership {h : Heap} {r : ZStreamRef} 
    (history : GenericDefaultRequestTrace r h) :
    ∃ before initialized version ds z d config,
      InitDomain before r version ∧
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before=.ok (Z_OK,initialized) ∧
      ds=before.nextBlk ∧ initialized.nalloc=before.nalloc+5 ∧
      DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) ∧
      DefaultFinishBoundary h r ds z d config ∧
      (∀ b, DeflateOwned ds d b ↔ before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → h.live b) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → ¬ before.live b) := by
  induction history with
  | @init before initialized version domain actual =>
      have domainCopy:=domain
      obtain ⟨hf,hu,hg,hv,z,hz,ha,_null⟩:=domain
      obtain ⟨zf,sf,state⟩:=observed_default_init_encoding_state hf hu hg hz ha hv actual
      obtain ⟨count,initial,_birthLive,initialLive,_oldLive⟩:=generic_default_initial_birth_ledger domainCopy actual
      have initialCopy:=initial
      obtain ⟨zi,di,goodI,_alloc,_free,_level,_strategy,_window,_hash,_wrap,_start,_look,_pending,
        _bits,_header,_totalIn,_totalOut,_message,_frame,_live,owned⟩:=initialCopy
      have states : di=sf := Option.some.inj (goodI.live.hs.symm.trans state.protocol.good.live.hs)
      subst di
      refine ⟨before,initialized,version,before.nextBlk,zf,sf,engineConfig sf,
        domainCopy,actual,rfl,count,initial,state.protocol,owned,?_,?_⟩
      · intro b lower upper
        exact (initialLive b lower upper).1
      · intro b lower upper
        exact (initialLive b lower upper).2
  | caller _ edit ih =>
      obtain ⟨before,initialized,version,ds,z,d,config,domain,actual,key,count,initial,state,owned,_live,fresh⟩:=ih
      obtain ⟨zg,_get,stateG⟩:=state.rebuffer edit
      refine ⟨before,initialized,version,ds,zg,d,config,domain,actual,key,count,initial,stateG,owned,?_,fresh⟩
      intro b lower upper
      exact owned_live stateG.good ((owned b).mpr ⟨lower,upper⟩)
  | step _ buffers run ih =>
      obtain ⟨before,initialized,version,ds,z,d,config,domain,actual,key,count,initial,state,owned,_live,fresh⟩:=ih
      obtain ⟨_used,_produced,_rc,computed,z',result,execution,stateA,_buffersA,_accountA,_allowed⟩:=
        state.generic_all_scalar_request buffers _
      have heaps : computed=_ := (Prod.mk.inj (Except.ok.inj (execution.symm.trans run))).2
      subst computed
      have ownedA : ∀ b, DeflateOwned ds result b ↔ before.nextBlk≤b ∧ b<before.nextBlk+5 := by
        intro b
        exact (state.generic_same_owned_keys stateA b).trans (owned b)
      refine ⟨before,initialized,version,ds,z',result,config,domain,actual,key,count,initial,stateA,ownedA,?_,fresh⟩
      intro b lower upper
      exact owned_live stateA.good ((ownedA b).mpr ⟨lower,upper⟩)
end Zlib.Deflate.Engine.Proofs
