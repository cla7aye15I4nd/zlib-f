import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-public-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-positive-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-physical»
import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-protocol»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Every real basic request has complete wrapping totals and physical effects
for all signed scalars and every public caller output representation. Actual
refusals and all capacities are included without a readable snapshot premise. -/
theorem DefaultFinishBoundary.generic_all_scalar_run_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (run : deflate (some r) flush h=.ok (rc,after)) (get : r.get after=some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  have rawCase (raw : z.next_out=.null ∨ ∃ ob oo,z.next_out=.ref (.blk ob) oo) :
      returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced ∧
        Shape h after ∧ BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
        LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
    obtain ⟨accepted,written,ret,computed,z',result,actual,stateA,_buffers,_good,counts,_bytes,tin,tout,
        _codes,_errors,_bad,_terminal,shape,frame,live,nalloc,next⟩ :=
      boundary.all_scalar_request_contract flush buffers raw
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst computed
    have streams : z'=returned := Option.some.inj (stateA.good.live.hz.symm.trans get)
    subst z'
    have amounts := stream_accounting_counts_unique counts account
    rw [amounts.1] at tin
    rw [amounts.2] at tout frame
    exact ⟨tin,tout,shape,frame,live,nalloc,next⟩
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact rawCase (Or.inl null)
  · exact rawCase (Or.inr raw)
  · by_cases bad : flush.toInt<0 ∨ 5<flush.toInt
    · have guard : flush>Z_BLOCK ∨ flush<0 := bad.elim
        (fun low => Or.inr (Int32.lt_iff_toInt_lt.mpr low)) (fun high => Or.inl (Int32.lt_iff_toInt_lt.mpr high))
      have actual := public_bad_flush_refusal boundary.good flush guard
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      subst after
      have streams : returned=z := Option.some.inj (get.symm.trans boundary.good.live.hz)
      subst returned
      have zeroIn : used=0 := by have counts:=account.2.2.1;omega
      have zeroOut : produced=0 := by have counts:=account.2.2.2.1;omega
      subst used produced
      have shape : Shape h h := by intro b;simp
      have frame : Frame h h (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) := by simp [Frame,SlotSame]
      have precise := finishing_foreign_private_zero_frame boundary.good buffers pointer shape frame
      exact ⟨by simp,by simp,shape,precise,full_shape_live_change shape,rfl,rfl⟩
    · by_cases finish : flush=Z_FINISH
      · subst flush
        by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
            (d.status=FINISH_STATE ∧ Z_FINISH≠Z_FINISH) ∨ z.avail_out=0
        · have counters := boundary.entry_refusal_run_counter_effects (by decide) (by decide) refused run get account
          obtain ⟨shape,frame,live,nalloc,next⟩ :=
            boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run
          have privateFrame : Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) :=
            full_frame_weaken frame (fun _ root=>Or.inl root)
          have precise := finishing_foreign_private_zero_frame boundary.good buffers pointer shape privateFrame
          have zeroOut : produced=0 := by
            obtain ⟨_ret,other,otherZ,_codes,actual,stateA,_buffers,counts⟩ :=
              boundary.entry_refusals Z_FINISH buffers (by decide) (by decide) refused
            have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
            subst other
            have streams : otherZ=returned := Option.some.inj (stateA.good.live.hz.symm.trans get)
            subst otherZ
            exact (stream_accounting_counts_unique counts account).2.symm
          exact ⟨counters.1,counters.2,shape,by simpa only [zeroOut] using precise,live,nalloc,next⟩
        · have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq=>refused (Or.inr (Or.inl ⟨count,eq⟩))
          have positive : 0<z.avail_out.toNat := by
            have ne : z.avail_out.toNat≠0 := fun eq=>refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp eq))))
            omega
          obtain ⟨tin,tout,shape,_frame,live,nalloc,next,precise⟩ :=
            boundary.foreign_finish_positive_run_effects buffers pointer positive valid run get account
          exact ⟨tin,tout,shape,precise,live,nalloc,next⟩
      · have flag : flush=Z_NO_FLUSH ∨ flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK := by
          have n4 : flush.toInt≠4 := fun eq=>finish (Int32.toInt_inj.mp eq)
          simp only [←Int32.toInt_inj]
          change flush.toInt=0 ∨ flush.toInt=1 ∨ flush.toInt=2 ∨ flush.toInt=3 ∨ flush.toInt=5
          omega
        obtain ⟨tin,tout,shape,_frame,live,nalloc,next,precise⟩ :=
          boundary.foreign_nonfinish_run_full_effects buffers pointer flush flag run get account
        exact ⟨tin,tout,shape,precise,live,nalloc,next⟩
end Zlib.Deflate.Engine.Proofs
