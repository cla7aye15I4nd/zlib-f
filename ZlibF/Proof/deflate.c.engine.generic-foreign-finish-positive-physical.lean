import ZlibF.Proof.«deflate.c.engine.generic-foreign-first-finish-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-busy-finish-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-run-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-new-input-run-physical»
import ZlibF.Proof.«deflate.c.engine.public-request-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every positive-output actual FINISH call over the original initialized protocol
has exact wrapping totals, real shape/allocation effects and the full foreign caller frame.
Initial headers, queued output, finishing and new-input refusal are all included. -/
theorem DefaultFinishBoundary.foreign_finish_positive_run_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (output : 0<z.avail_out.toNat)
    (valid : z.avail_in≠0 → z.next_in≠.null)
    (run : deflate (some r) Z_FINISH h=.ok (rc,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have identify {accepted delivered : Nat} {other : Heap} {otherZ : ZStream} {otherD : DeflateState} {otherRc : Int32}
      (actual : deflate (some r) Z_FINISH h=.ok (otherRc,other)) (goodA : DGood other r ds otherZ otherD)
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
      public_foreign_first_finish_full_storage_execution initial level state buffers pointer output boundary.configuration.memory valid
    exact identify actual goodA counts inputA outputA physical
  · obtain ⟨input,origin,base,xs,state,status⟩ := working
    have level : d.level=6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
    have strategy : d.strategy=0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
    obtain ⟨_used,_produced,_rc,_heap,_z,_d,actual,goodA,counts,inputA,outputA,physical⟩ :=
      public_foreign_busy_finish_full_storage_execution state buffers status level strategy pointer boundary.configuration.memory
        boundary.configuration.wrap output valid boundary.lower boundary.upper
    exact identify actual goodA counts inputA outputA physical
  · by_cases empty : z.avail_in=0
    · have acceptedZero : used=0 := by
        have count := account.2.2.1
        rw [empty] at count
        change returned.avail_in.toNat+used=0 at count
        omega
      have effects := public_foreign_finishing_run_full_storage boundary.good buffers finishing pointer empty output
        boundary.lower boundary.upper run live account
      simpa [acceptedZero] using effects
    · exact public_foreign_finishing_new_input_run_full_storage boundary.good buffers finishing pointer valid empty output
        boundary.lower boundary.upper run live account

end Zlib.Deflate.Engine.Proofs
