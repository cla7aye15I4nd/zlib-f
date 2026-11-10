import ZlibF.Proof.«deflate.c.engine.public-source»

/-! # Pure source proofs of public entry refusals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual public pre-store stream guard returns STREAM_ERROR. -/
theorem public_stream_guard_refusal {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (flush : Int32)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (bad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) :
    deflate (some r) flush h = ERR_RETURN (some r) Z_STREAM_ERROR h := by
  have flagUpper : ¬ flush > Z_BLOCK := by
    change ¬ Z_BLOCK < flush
    rw [Int32.lt_iff_toInt_lt]
    omega
  have flagLower : ¬ flush < 0 := by
    rw [Int32.lt_iff_toInt_lt]
    change ¬ flush.toInt < 0
    omega
  have guard : (z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH)) = true := by
    rcases bad with out | ⟨nonempty, input⟩ | ⟨status, flag⟩
    · simp [out]
    · simp [nonempty, input]
    · simp [status, flag]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    flagUpper, flagLower, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs, guard, ite_true]

/-- Zero public output is refused before private state mutation. -/
theorem public_zero_output_refusal {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (flush : Int32)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (finish : d.status = FINISH_STATE → flush = Z_FINISH) (empty : z.avail_out = 0) :
    deflate (some r) flush h = ERR_RETURN (some r) Z_BUF_ERROR h := by
  have flagUpper : ¬ flush > Z_BLOCK := by
    change ¬ Z_BLOCK < flush
    rw [Int32.lt_iff_toInt_lt]
    omega
  have flagLower : ¬ flush < 0 := by
    rw [Int32.lt_iff_toInt_lt]
    change ¬ flush.toInt < 0
    omega
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases zero : z.avail_in = 0
    · simp [zero]
    · simp [input zero]
  have finishAllowed : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
    by_cases status : d.status = FINISH_STATE
    · simp [status, finish status]
    · simp [status]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    flagUpper, flagLower, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, finishAllowed, Bool.or_false, empty, BEq.rfl, ite_true]

/-- Every out-of-range signed flush flag is refused without changing even the message. -/
theorem public_bad_flush_refusal {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (flush : Int32) (bad : flush > Z_BLOCK ∨ flush < 0) :
    deflate (some r) flush h = .ok (Z_STREAM_ERROR, h) := by
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  rcases bad with high | low
  · simp [bind_app, pure_app, checked, high]
  · simp [bind_app, pure_app, checked, low]

end Zlib.Deflate.Engine.Proofs
