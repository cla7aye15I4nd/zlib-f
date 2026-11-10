import ZlibF.Proof.«deflate.c.engine.public-rank»

/-! # Actual finished-state new-input checks before data dispatch -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- With no queued bytes, new input in FINISH_STATE is refused after
the actual flush-marker store and before header/data dispatch. -/
theorem public_finished_new_input_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = FINISH_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.next_in ≠ .null) (nonempty : z.avail_in ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    deflate (some r) Z_FINISH h =
      ERR_RETURN (some r) Z_BUF_ERROR (setD h ds { d with last_flush := Z_FINISH }) := by
  obtain ⟨rank, ranked⟩ := public_rank_request_total d.last_flush lower upper
  have checked := stateCheck_live good.live
  have rankFinish : RANK Z_FINISH = pure 8 := rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    show (z.next_in == .null) = false from beq_eq_false_iff_ne.mpr input,
    Bool.and_false, Bool.or_false, show (Z_FINISH != Z_FINISH) = false from rfl,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl,
    rankFinish, ranked, Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD,
    status, BEq.rfl, show (z.avail_in != 0) = true from bne_iff_ne.mpr nonempty, Bool.true_and, ite_true]

/-- Queued output drains before the finished/new-input check. If room
remains, that actual check refuses the new input on the returned heap. -/
theorem public_pending_finish_new_input_source {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_FINISH }) = .ok ((), middle))
    (remaining : zm.avail_out ≠ 0) (finished : result.status = FINISH_STATE) (newInput : zm.avail_in ≠ 0) :
    deflate (some r) Z_FINISH h = ERR_RETURN (some r) Z_BUF_ERROR middle := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (Z_FINISH != Z_FINISH) = false from rfl, Bool.and_false, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz,
    show (zm.avail_out == 0) = false from beq_eq_false_iff_ne.mpr remaining,
    rdD_eq, goodM.live.hs, finished, BEq.rfl,
    show (zm.avail_in != 0) = true from bne_iff_ne.mpr newInput, Bool.true_and]

end Zlib.Deflate.Engine.Proofs
