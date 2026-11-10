import ZlibF.Proof.«deflate.c.engine.valid-flush-entry»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every valid rank is above the actual reset sentinel. -/
theorem valid_flush_initial_rank (flush : Int32) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) :
    ∃ current, RANK flush = pure current ∧ ¬ current ≤ (-4 : Int32) := by
  have values : flush = 0 ∨ flush = 1 ∨ flush = 2 ∨ flush = 3 ∨ flush = 4 ∨ flush = 5 := by
    have values : flush.toInt = 0 ∨ flush.toInt = 1 ∨ flush.toInt = 2 ∨ flush.toInt = 3 ∨ flush.toInt = 4 ∨ flush.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact values
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, by decide⟩

/-- The actual initialized entry accepts every valid request, including
empty input, since its reset rank is below every legal flush rank. -/
theorem public_default_valid_initial_entry {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) flush)
        (setD h ds { d with last_flush := flush }) := by
  have checked := stateCheck_live start.good.live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  obtain ⟨current, rank0, nonnegative⟩ := valid_flush_initial_rank flush flushLow flushHigh
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  have rankOld : RANK (-2) = pure (-4) := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, start.good.live.hz, start.good.live.zst, castDeflateState,
    ldZStream_ok start.good.live.hz, ldDeflateState_tab start.good.live.hs, inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    start.status, show (INIT_STATE == FINISH_STATE) = false from by decide,
    Bool.false_and, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, start.good.live.hs, start.pending, show ((0 : UInt64) != 0) = false from rfl,
    start.lastFlush, rank0, rankOld, nonnegative, decide_false,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]

end Zlib.Deflate.Engine.Proofs
