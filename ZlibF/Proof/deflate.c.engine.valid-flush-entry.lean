import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-buffered»
/-! # Actual BUSY entry for every valid flush request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every valid request with new input passes the actual BUSY entry and
records its flush. Both rank computations are established from their legal
ranges; no rank or strategy contract is assumed. -/
theorem public_busy_valid_nonempty_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) (nonempty : z.avail_in ≠ 0)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h =
      publicDataTail (some r) (some (.tab ds)) flush
        (setD h ds { d with last_flush := flush }) := by
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) flush)
      (setD h ds { d with last_flush := flush }) =
      publicDataTail (some r) (some (.tab ds)) flush (setD h ds { d with last_flush := flush }) := by
    unfold publicZlibHeader
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live good.live
  obtain ⟨current, rankedCurrent⟩ := rank_legal_last_flush flush (by omega) flushHigh
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
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending,
    show (z.avail_in == 0) = false from beq_eq_false_iff_ne.mpr nonempty, Bool.false_and, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankedCurrent, ranked,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  simpa only [status, pending] using header
/-- The complete valid BUSY entry includes empty-input duplicate refusal.
The numerical ranks are computed by their actual total source, and every
accepted branch reaches the real data tail after recording the request. -/
theorem public_busy_valid_entry_choice {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    ∃ current old,
      RANK flush = pure current ∧ RANK d.last_flush = pure old ∧
      deflate (some r) flush h =
        if (z.avail_in == 0 && decide (current ≤ old) && flush != Z_FINISH) then
          ERR_RETURN (some r) Z_BUF_ERROR (setD h ds { d with last_flush := flush })
        else publicDataTail (some r) (some (.tab ds)) flush (setD h ds { d with last_flush := flush }) := by
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) flush)
      (setD h ds { d with last_flush := flush }) =
      publicDataTail (some r) (some (.tab ds)) flush (setD h ds { d with last_flush := flush }) := by
    unfold publicZlibHeader
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live good.live
  obtain ⟨current, rankedCurrent⟩ := rank_legal_last_flush flush (by omega) flushHigh
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  refine ⟨current, rank, rankedCurrent, ranked, ?_⟩
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending,
    show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankedCurrent, ranked,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  by_cases duplicate : (z.avail_in == 0 && decide (current ≤ rank) && flush != Z_FINISH) = true
  · simp only [duplicate, ite_true]
  · have notDuplicate := Bool.eq_false_iff.mpr duplicate
    simp only [notDuplicate, Bool.false_eq_true, ite_false, bind_app, rdD_eq,
      setD_dstates_same, zrd_eq, ZStreamRef.get_setD, good.live.hz,
      show (BUSY_STATE == FINISH_STATE) = false from rfl,
      Bool.false_and]
    simpa only [status, pending] using header
end Zlib.Deflate.Engine.Proofs
