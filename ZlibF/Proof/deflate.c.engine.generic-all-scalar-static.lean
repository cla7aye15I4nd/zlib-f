import ZlibF.Proof.«deflate.c.engine.generic-request-trace-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-positive-physical»
import ZlibF.Proof.«deflate.c.default-core-rebuffer»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual basic request retains library tables, for every signed flag,
all caller outputs, zero capacity and unreadable-input refusals. -/
theorem DefaultFinishBoundary.generic_all_scalar_run_static {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (run : deflate (some r) flush h=.ok (rc,after)) : after.static=h.static := by
  have rawCase (raw : z.next_out=.null ∨ ∃ ob oo,z.next_out=.ref (.blk ob) oo) : after.static=h.static := by
    obtain ⟨_used,written,_rc,computed,z',result,actual,stateA,_buffers,_good,_account,_bytes,_in,_out,
        _codes,_errors,_bad,_terminal,_shape,frame,_live,_nalloc,_next⟩ :=
      boundary.all_scalar_request_contract flush buffers raw
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst computed
    exact (ZlibF.Spec.Public.Proofs.DeflateCore.raw_frame_static raw frame).symm
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact rawCase (Or.inl null)
  · exact rawCase (Or.inr raw)
  · by_cases bad : flush.toInt<0 ∨ 5<flush.toInt
    · have guard : flush>Z_BLOCK ∨ flush<0 := bad.elim
        (fun low => Or.inr (Int32.lt_iff_toInt_lt.mpr low)) (fun high => Or.inl (Int32.lt_iff_toInt_lt.mpr high))
      have actual := public_bad_flush_refusal boundary.good flush guard
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
      subst after
      rfl
    · by_cases noflush : flush=Z_NO_FLUSH
      · subst flush
        exact boundary.foreign_no_flush_run_static buffers pointer run
      · by_cases finish : flush=Z_FINISH
        · subst flush
          by_cases refused : z.next_out=.null ∨ (z.avail_in≠0 ∧ z.next_in=.null) ∨
              (d.status=FINISH_STATE ∧ Z_FINISH≠Z_FINISH) ∨ z.avail_out=0
          · exact (boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run).2.1.1.symm
          · have valid : z.avail_in≠0 → z.next_in≠.null := fun count eq => refused (Or.inr (Or.inl ⟨count,eq⟩))
            have positive : 0<z.avail_out.toNat := by
              have nonzero : z.avail_out.toNat≠0 := fun eq => refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp eq))))
              omega
            obtain ⟨_used,_produced,_rc,computed,z',result,actual,stateA,_buffers,account,_codes⟩ :=
              boundary.generic_all_scalar_request buffers Z_FINISH
            have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
            subst computed
            have effects := boundary.foreign_finish_positive_run_effects buffers pointer positive valid run stateA.good.live.hz account
            exact effects.2.2.2.1.1.symm
        · have marker : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK := by
            have n0 : flush.toInt≠0 := fun eq => noflush (Int32.toInt_inj.mp eq)
            have n4 : flush.toInt≠4 := fun eq => finish (Int32.toInt_inj.mp eq)
            simp only [←Int32.toInt_inj]
            change flush.toInt=1 ∨ flush.toInt=2 ∨ flush.toInt=3 ∨ flush.toInt=5
            omega
          exact boundary.foreign_marker_run_static buffers pointer flush marker run

/-- Every basic request history derives retained library globals from actual
init and source frames, with no readable-input or caller environment premise. -/
theorem GenericDefaultRequestTrace.globals {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) : LibraryGlobals h := by
  induction history with
  | init domain actual => exact ZlibF.Spec.Public.Proofs.DeflateCore.initialized_globals domain actual
  | caller _ edit _ih => exact edit.2.2.1
  | step previous buffers actual ih =>
      obtain ⟨ds,z,d,config,boundary⟩ := previous.protocol
      exact (boundary.generic_all_scalar_run_static buffers actual).trans ih

/-- Observed all-signed histories inherit globals through the genuine one-way
embedding into basic request history, without weakening either trace. -/
theorem GenericDefaultDataTrace.all_scalar_globals {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) : LibraryGlobals h := history.request_trace.globals
end Zlib.Deflate.Engine.Proofs
