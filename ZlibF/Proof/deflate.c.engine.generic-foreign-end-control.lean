import ZlibF.Proof.«deflate.c.engine.generic-request-birth-cleanup»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual END with foreign caller output derives the original accepted
FINISH protocol and terminal fields. Neither output capacity nor input acceptance
nor the terminal state is assumed by the caller. -/
theorem DefaultFinishBoundary.generic_foreign_finish_end_run_control
    {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z returned : ZStream} {d result : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (actual : deflate (some r) Z_FINISH h=.ok (Z_STREAM_END,after))
    (goodA : DGood after r ds returned result) :
    result.status=FINISH_STATE ∧ returned.avail_in=0 ∧ result.pending=0 ∧ result.bi_valid=0 := by
  by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
      (d.status=FINISH_STATE ∧ Z_FINISH≠Z_FINISH) ∨ z.avail_out=0
  · obtain ⟨err,middle,zm,allowed,run,_state,_buffers,_account⟩ :=
      boundary.entry_refusals Z_FINISH buffers (by decide) (by decide) refused
    have code : err=Z_STREAM_END := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
    have noEnd : err≠Z_STREAM_END := by rcases allowed with rfl|rfl <;> decide
    exact False.elim (noEnd code)
  · have valid : z.avail_in≠0 → z.next_in≠.null :=
      fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
    have nonzero : z.avail_out≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0<z.avail_out.toNat := by
      have count : z.avail_out.toNat≠0 := fun eq => nonzero (UInt32.toNat_inj.mp eq)
      omega
    by_cases newInput : d.status=FINISH_STATE ∧ z.avail_in≠0
    · have phase : FinishingPhase d config := by
        rcases boundary.phase with ⟨_input,_origin,_base,start,_state⟩|working|finishing
        · exact False.elim ((by decide : INIT_STATE≠FINISH_STATE) (start.status.symm.trans newInput.1))
        · obtain ⟨_input,_origin,_base,_xs,_state,status⟩:=working
          exact False.elim ((by decide : BUSY_STATE≠FINISH_STATE) (status.symm.trans newInput.1))
        · exact finishing
      obtain ⟨_produced,rc,middle,zm,dm,run,_good,_buffers,_account,allowed,_phase,_last,_input,_exhausted⟩ :=
        public_default_foreign_finishing_new_input boundary.good buffers phase pointer valid newInput.2 output boundary.lower boundary.upper
      have code : rc=Z_STREAM_END := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      have noEnd : rc≠Z_STREAM_END := by rcases allowed with rfl|rfl <;> decide
      exact False.elim (noEnd code)
    · have accepted : d.status=FINISH_STATE → z.avail_in=0 := by
        intro status
        by_cases empty : z.avail_in=0
        · exact empty
        · exact False.elim (newInput ⟨status,empty⟩)
      obtain ⟨_used,_produced,rc,middle,zm,dm,run,stateA,_buffers,_account,_codes,terminal⟩ :=
        boundary.foreign_finish buffers pointer output valid accepted
      obtain ⟨code,heap⟩:=Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
      subst rc middle
      have streams : zm=returned:=Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
      have states : dm=result:=Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
      subst zm dm
      have ended:=terminal rfl
      exact ⟨ended.1,ended.2.2.1,ended.2.2.2.2.1,Int32.toInt_inj.mp ended.2.2.2.2.2⟩
end Zlib.Deflate.Engine.Proofs
