import ZlibF.Proof.«deflate.c.universal-call-cont»
import ZlibF.Proof.«deflate.c.universal-flush-cursor»

/-!
# deflate.c: the entry phase with output pending, at any cursor

Owner 2 of the deflate split (`deflate_call`). With output pending, the entry phase stores
`last_flush := flush` and runs `flush_pending` at whatever cursor the previous call left. Then it
returns `Z_OK` on a full output, refuses new input after `Z_FINISH`, or continues. This module
evaluates the entry phase in terms of the flush's run (no cursor premise).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **The entry phase with output pending**, given the run of its flush. -/
theorem entry_pending_eval {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (accepted : ¬ DeflateRefuses z d flush)
    (avail : z.avail_out ≠ 0) (pending : d.pending ≠ 0) {after : Heap} {z' : ZStream} {d' : DeflateState}
    (run : flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after))
    (hz : r.get after = some z') (hs : after.dstates ds = some d') (k : DeflateStatePtr → M Int32) :
    entryPhase (some r) flush k h =
      if z'.avail_out = 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 })
      else if d'.status = FINISH_STATE ∧ z'.avail_in ≠ 0 then ERR_RETURN (some r) Z_BUF_ERROR after
      else k (some (.tab ds)) after := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have fin : ¬ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
    fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inr e))))
  have finTest : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
    by_cases st : d.status = FINISH_STATE
    · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
      simp [st, this]
    · simp [st]
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags flushLow flushHigh
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, finTest,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr avail,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending, ite_true, run]
  by_cases full : z'.avail_out = 0
  · simp [zrd_eq, hz, full, wrD_eq, hs, bind_app]
  · by_cases c : d'.status = FINISH_STATE ∧ z'.avail_in ≠ 0
    · simp [zrd_eq, hz, full, rdD_eq, hs, bind_app, c.1, c.2]
    · rw [if_neg full, if_neg c]
      simp [zrd_eq, hz, full, rdD_eq, hs, bind_app]
      split
      · rename_i t
        exact absurd ⟨t.1, t.2⟩ c
      · rfl

end Zlib.Deflate.Universal.Call
