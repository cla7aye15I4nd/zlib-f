import ZlibF.Proof.«deflate.c.engine.public-strategy-source»

/-! # Public slow dispatch for compression levels four through nine -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The admitted slow levels are exactly the six actual table indices. -/
theorem slow_level_cases {level : Int32} (low : 4 ≤ level.toInt) (high : level.toInt ≤ 9) :
    level = 4 ∨ level = 5 ∨ level = 6 ∨ level = 7 ∨ level = 8 ∨ level = 9 := by
  have values : level.toInt = 4 ∨ level.toInt = 5 ∨ level.toInt = 6 ∨
      level.toInt = 7 ∨ level.toInt = 8 ∨ level.toInt = 9 := by omega
  rcases values with h | h | h | h | h | h
  · exact Or.inl (Int32.toInt_inj.mp h)
  · exact Or.inr (Or.inl (Int32.toInt_inj.mp h))
  · exact Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp h)))))

/-- The translated table selects slow at every level from four to nine. -/
theorem common_slow_config_func {level : Int32}
    (low : 4 ≤ level.toInt) (high : level.toInt ≤ 9) :
    configuration_table[level.toInt.toNat]!.func = .slow := by
  rcases slow_level_cases low high with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 2500000 in
/-- `int deflate(z_streamp strm, int flush)` (BUSY FINISH dispatch).
The actual public data path at each slow compression level executes the
translated slow engine and its public return statements. No execution
contract, default-level equality or replacement translation is assumed. -/
theorem public_busy_common_slow_finish_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (strategy : d.strategy = 0) :
    publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      (do let bstate ← deflate_slow (some (.tab ds)) Z_FINISH
          publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH bstate) h := by
  have cfg : config_at d.level = pure configuration_table[d.level.toInt.toNat]! := by
    funext heap
    exact config_at_run heap (by omega) high
  have selected := common_slow_config_func low high
  have nonzero : d.level ≠ 0 := by
    intro zero
    rw [zero] at low
    change (4 : Int) ≤ 0 at low
    omega
  unfold publicDataTail publicStrategyReturn publicFinishTail zlibTrailer
  simp only [M_bind_assoc]
  simp only [bind_app, pure_app, rdD_eq, hs, status,
    show (BUSY_STATE == GZIP_STATE) = false from by decide,
    show (BUSY_STATE == EXTRA_STATE) = false from by decide,
    show (BUSY_STATE == NAME_STATE) = false from by decide,
    show (BUSY_STATE == COMMENT_STATE) = false from by decide,
    show (BUSY_STATE == HCRC_STATE) = false from by decide,
    Bool.false_eq_true, ite_false, ldDeflateState_tab hs,
    zrd_eq, hz, show (Z_FINISH != Z_NO_FLUSH) = true from rfl,
    show (BUSY_STATE != FINISH_STATE) = true from rfl,
    Bool.true_and, Bool.or_true, ite_true,
    strategy, show (d.level == 0) = false from beq_eq_false_iff_ne.mpr nonzero,
    show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
    show ((0 : Int32) == Z_RLE) = false from rfl, cfg, selected]

end Zlib.Deflate.Engine.Proofs
