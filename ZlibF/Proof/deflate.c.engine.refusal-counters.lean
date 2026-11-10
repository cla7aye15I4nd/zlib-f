import ZlibF.Proof.«deflate.c.engine.counter-effects»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»
import ZlibF.Proof.«deflate.c.engine.no-flush-duplicate»

/-! # Actual message stores and public refusals retain exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real static error lookup and message store retain both totals. -/
theorem err_return_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {z returned : ZStream} {err rc : Int32} {used produced : Nat}
    (live : r.get h = some z) (run : ERR_RETURN (some r) err h = .ok (rc, after))
    (returnedLive : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨message, expected⟩ := err_return_run live err
  have get := ZStreamRef.get_put_same live { z with msg := message }
  have same := actual_run_stream_unique expected run get returnedLive
  have known : StreamAccounting z { z with msg := message } 0 0 := stream_accounting_zero z
  exact stream_counter_effects_identify same known account (by simp) (by simp)

/-- Every legal-flag entry refusal has exact zero movement and total effects. -/
theorem DefaultFinishBoundary.entry_refusal_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases streamBad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · have source := public_stream_guard_refusal boundary.good flush flagLo flagHi streamBad
    exact err_return_run_counter_effects boundary.good.live.hz (source.symm.trans run) live account
  · have out : z.next_out ≠ .null := fun eq => streamBad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => streamBad (Or.inr (Or.inl ⟨count, eq⟩))
    have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
      intro status
      by_cases flag : flush = Z_FINISH
      · exact flag
      · exact False.elim (streamBad (Or.inr (Or.inr ⟨status, flag⟩)))
    have empty : z.avail_out = 0 := by
      rcases refused with bad | bad | bad | empty
      · exact False.elim (out bad)
      · exact False.elim (valid bad.1 bad.2)
      · exact False.elim (bad.2 (finish bad.1))
      · exact empty
    have source := public_zero_output_refusal boundary.good flush flagLo flagHi out valid finish empty
    exact err_return_run_counter_effects boundary.good.live.hz (source.symm.trans run) live account

/-- The duplicate-request refusal also retains totals after recording NO_FLUSH. -/
theorem public_duplicate_no_flush_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {rc : Int32}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE)
    (input : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : 0 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  have source := public_busy_no_flush_duplicate_source good status input pending out positive lower upper
  have get : r.get (setD h ds { d with last_flush := Z_NO_FLUSH }) = some z := by
    simpa only [ZStreamRef.get_setD] using good.live.hz
  exact err_return_run_counter_effects get (source.symm.trans run) live account

end Zlib.Deflate.Engine.Proofs
