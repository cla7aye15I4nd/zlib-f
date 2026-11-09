import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-first-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-busy-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-physical»
import ZlibF.Proof.«deflate.c.engine.public-request-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual non-FINISH call over the original initialized protocol has exact
wrapping totals, real shape/allocation effects and the full foreign caller frame.
All capacities, initial headers, queued output, duplicate and entry refusals are included. -/
theorem DefaultFinishBoundary.foreign_nonfinish_run_full_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (flush : Int32) (flag : flush=Z_NO_FLUSH ∨ flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK)
    (run : deflate (some r) flush h=.ok (rc,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide
  have nonfinal : flush≠Z_FINISH := by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide
  by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
      (d.status=FINISH_STATE ∧ flush≠Z_FINISH) ∨ z.avail_out=0
  · have counters := boundary.entry_refusal_run_counter_effects flagLo flagHi refused run live account
    obtain ⟨shape,frame,liveA,alloc,next⟩ := boundary.entry_refusal_run_full_storage flagLo flagHi refused run
    have privateFrame : Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) :=
      full_frame_weaken frame (fun _ yes => Or.inl yes)
    have precise := finishing_foreign_private_zero_frame boundary.good buffers pointer shape privateFrame
    have producedZero : produced=0 := by
      obtain ⟨err,other,otherZ,_allowed,tested,stateA,_buffersA,counts⟩ := boundary.entry_refusals flush buffers flagLo flagHi refused
      have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      subst other
      have streams : otherZ=returned := Option.some.inj (stateA.good.live.hz.symm.trans live)
      subst otherZ
      exact (stream_accounting_counts_unique counts account).2.symm
    exact ⟨counters.1,counters.2,shape,full_private_frame_add_output privateFrame,liveA,alloc,next,by simpa only [producedZero] using precise⟩
  · have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
    have unfinished : d.status≠FINISH_STATE := fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq,nonfinal⟩)))
    have nonzero : z.avail_out≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0<z.avail_out.toNat := by
      have neq : z.avail_out.toNat≠0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    have identify {accepted delivered : Nat} {other : Heap} {otherZ : ZStream} {otherD : DeflateState} {otherRc : Int32}
        (actual : deflate (some r) flush h=.ok (otherRc,other)) (goodA : DGood other r ds otherZ otherD)
        (counts : StreamAccounting z otherZ accepted delivered)
        (inputA : otherZ.total_in=z.total_in+UInt64.ofNat accepted)
        (outputA : otherZ.total_out=z.total_out+UInt64.ofNat delivered)
        (physical : Shape h other ∧ Frame h other (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
          LiveChange h other (fun _ => False) (fun _ => False) ∧ other.nalloc=h.nalloc ∧ other.nextBlk=h.nextBlk ∧
          BufferFrame h other (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,delivered⟩]) :
        returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced ∧
          Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
          LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
          BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      subst other
      have streams : otherZ=returned := Option.some.inj (goodA.live.hz.symm.trans live)
      subst otherZ
      have amounts := stream_accounting_counts_unique counts account
      rw [amounts.1] at inputA
      rw [amounts.2] at outputA physical
      exact ⟨inputA,outputA,physical⟩
    rcases boundary.phase with ⟨input,origin,base,initial,state⟩ | working | finishing
    · have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨_used,_produced,_rc,_heap,_z,_d,actual,goodA,counts,inputA,outputA,physical⟩ :=
        public_foreign_first_nonfinish_full_storage_execution initial level state buffers pointer output boundary.configuration.memory valid flush flag
      exact identify actual goodA counts inputA outputA physical
    · obtain ⟨input,origin,base,xs,state,status⟩ := working
      have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy=0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨_used,_produced,_rc,_heap,_z,_d,actual,goodA,counts,inputA,outputA,physical⟩ :=
        public_foreign_busy_nonfinish_full_storage_execution state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper flush flag
      exact identify actual goodA counts inputA outputA physical
    · exact False.elim (unfinished finishing.status)

end Zlib.Deflate.Engine.Proofs
