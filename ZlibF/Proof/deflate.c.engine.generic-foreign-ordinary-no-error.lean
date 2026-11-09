import ZlibF.Proof.«deflate.c.engine.generic-stream-end-control»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual foreign-output ordinary producers return no STREAM_ERROR after
entry guards pass. Its positive-output and accepted-finish guards are derived
inside the complete public return-code classifier. -/
theorem DefaultFinishBoundary.generic_foreign_ordinary_no_error
    {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (flag : flush=Z_NO_FLUSH ∨ flush=Z_FINISH) (positive : 0<z.avail_out.toNat)
    (valid : z.avail_in≠0 → z.next_in≠.null) (finishAllowed : d.status=FINISH_STATE → flush=Z_FINISH)
    (actual : deflate (some r) flush h=.ok (rc,after)) : rc≠Z_STREAM_ERROR := by
  rcases flag with rfl|rfl
  · have unfinished : d.status≠FINISH_STATE := by
      intro status
      exact (by decide : Z_NO_FLUSH≠Z_FINISH) (finishAllowed status)
    by_cases resume : d.pending≠0 ∨ z.avail_in≠0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
    · obtain ⟨_used,_produced,_middle,_zm,_dm,run,_state,_buffers,_account,_status⟩:=
        boundary.foreign_no_flush_resuming buffers pointer positive valid (fun _=>resume) unfinished
      have code : Z_OK=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      rw [←code]
      decide
    · have pending : d.pending=0 := by
        by_cases yes : d.pending=0
        · exact yes
        · exact False.elim (resume (Or.inl yes))
      have input : z.avail_in=0 := by
        by_cases yes : z.avail_in=0
        · exact yes
        · exact False.elim (resume (Or.inr (Or.inl yes)))
      have lower : 0≤d.last_flush.toInt := by
        have lo:=boundary.lower
        have notRetry : d.last_flush.toInt≠ -1 := fun eq=>resume (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp eq))))
        have notInitial : d.last_flush.toInt≠ -2 := fun eq=>resume (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp eq))))
        omega
      have status : d.status=BUSY_STATE := by
        rcases boundary.phase with ⟨_input,_origin,_base,start,_state⟩|working|finishing
        · exact False.elim (resume (Or.inr (Or.inr (Or.inr start.lastFlush))))
        · obtain ⟨_input,_origin,_base,_xs,_state,status⟩:=working
          exact status
        · exact False.elim (unfinished finishing.status)
      have nonnull : z.next_out≠.null := by rw [pointer];intro impossible;cases impossible
      have nonzero : z.avail_out≠0 := by intro zero;rw [zero] at positive;contradiction
      obtain ⟨_middle,_zm,run,_state,_buffers,_account⟩:=
        boundary.duplicate_no_flush buffers status input pending nonnull nonzero lower
      have code : Z_BUF_ERROR=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      rw [←code]
      decide
  · by_cases newInput : d.status=FINISH_STATE ∧ z.avail_in≠0
    · have phase : FinishingPhase d config := by
        rcases boundary.phase with ⟨_input,_origin,_base,start,_state⟩|working|finishing
        · exact False.elim ((by decide : INIT_STATE≠FINISH_STATE) (start.status.symm.trans newInput.1))
        · obtain ⟨_input,_origin,_base,_xs,_state,status⟩:=working
          exact False.elim ((by decide : BUSY_STATE≠FINISH_STATE) (status.symm.trans newInput.1))
        · exact finishing
      obtain ⟨_produced,ret,_middle,_zm,_dm,run,_good,_buffers,_account,codes,_phase,_last,_input,_exhausted⟩:=
        public_default_foreign_finishing_new_input boundary.good buffers phase pointer valid newInput.2 positive boundary.lower boundary.upper
      have code : ret=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      rw [code] at codes
      rcases codes with rfl|rfl <;> decide
    · have accepted : d.status=FINISH_STATE → z.avail_in=0 := by
        intro finished
        by_cases empty : z.avail_in=0
        · exact empty
        · exact False.elim (newInput ⟨finished,empty⟩)
      obtain ⟨_used,_produced,ret,_middle,_zm,_dm,run,_state,_buffers,_account,codes,_terminal⟩:=
        boundary.foreign_finish buffers pointer positive valid accepted
      have code : ret=rc:=(Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).1
      rw [code] at codes
      rcases codes with rfl|rfl <;> decide
end Zlib.Deflate.Engine.Proofs
