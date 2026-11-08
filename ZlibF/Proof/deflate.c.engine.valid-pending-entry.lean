import ZlibF.Proof.«deflate.c.engine.valid-flush-entry»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- After actual old-pending publication, every legal request continues
past the original duplicate check. The actual successful publication run
is supplied by its proved caller-buffer theorem. -/
theorem public_pending_valid_continue {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result) (status : d.status = BUSY_STATE)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5)
    (run : flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), middle))
    (remaining : zm.avail_out ≠ 0) (finishedInput : result.status = FINISH_STATE → zm.avail_in = 0) :
    deflate (some r) flush h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) flush) middle := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have finishInput : (result.status == FINISH_STATE && zm.avail_in != 0) = false := by
    by_cases status : result.status = FINISH_STATE
    · simp [status, finishedInput status]
    · simp [status]
  have checked := stateCheck_live good.live
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (d.status == FINISH_STATE) = false from by rw [status]; rfl,
    Bool.false_and, Bool.and_false, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz,
    show (zm.avail_out == 0) = false from beq_eq_false_iff_ne.mpr remaining,
    rdD_eq, goodM.live.hs, finishInput]


/-- A BUSY stream skips the wrapper header before any following action. -/
theorem public_busy_header_skip_next {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (next : M Int32) :
    publicZlibHeader (some r) (some (.tab ds)) next h = next h := by
  unfold publicZlibHeader
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]

end Zlib.Deflate.Engine.Proofs
