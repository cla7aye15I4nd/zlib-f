import ZlibF.Proof.«deflate.c.engine.public-source»

/-! # The actual duplicate-request prefix returns BUF_ERROR -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A zero-input repeated NO_FLUSH request with no pending bytes is
refused after recording the requested flush, as in the real source. -/
theorem public_busy_no_flush_duplicate_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE)
    (input : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : 0 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    deflate (some r) Z_NO_FLUSH h =
      ERR_RETURN (some r) Z_BUF_ERROR (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
  have values : d.last_flush = 0 ∨ d.last_flush = 1 ∨ d.last_flush = 2 ∨
      d.last_flush = 3 ∨ d.last_flush = 4 ∨ d.last_flush = 5 := by
    have : d.last_flush.toInt = 0 ∨ d.last_flush.toInt = 1 ∨ d.last_flush.toInt = 2 ∨
      d.last_flush.toInt = 3 ∨ d.last_flush.toInt = 4 ∨ d.last_flush.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  have rankOld : ∃ rank, RANK d.last_flush = pure rank ∧ (0 : Int32) ≤ rank := by
    rcases values with value | value | value | value | value | value <;> rw [value]
    all_goals exact ⟨_, rfl, by decide⟩
  obtain ⟨rank, ranked, nonnegative⟩ := rankOld
  have checked := stateCheck_live good.live
  have rankZero : RANK Z_NO_FLUSH = pure 0 := rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide, show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    input, show ((0 : UInt32) != 0) = false from rfl, Bool.false_and, Bool.or_false,
    status, show (BUSY_STATE == FINISH_STATE) = false from rfl,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankZero, ranked, nonnegative, decide_true,
    show (Z_NO_FLUSH != Z_FINISH) = true from rfl, Bool.true_and, ite_true]

end Zlib.Deflate.Engine.Proofs
