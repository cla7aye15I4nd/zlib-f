import ZlibF.Proof.«deflate.c.engine.public-no-flush-source»
import ZlibF.Proof.«deflate.c.engine.common-slow-source»

/-! # Actual NO_FLUSH dispatch for slow levels four through nine -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 2500000 in
/-- Actual active default NO_FLUSH data dispatch reaches the slow strategy. -/
theorem public_common_slow_no_flush_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9)
    (strategy : d.strategy = 0)
    (active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0) :
    publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
      (do let bstate ← deflate_slow (some (.tab ds)) Z_NO_FLUSH
          publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH bstate) h := by
  have cfg : config_at d.level = pure configuration_table[d.level.toInt.toNat]! := by
    funext heap
    exact config_at_run heap (by omega) high
  have selected := common_slow_config_func low high
  have nonzero : d.level ≠ 0 := by
    intro zero
    rw [zero] at low
    change (4 : Int) ≤ 0 at low
    omega
  have activeBool : (z.avail_in != 0 || d.lookahead != 0) = true := by
    rcases active with input | look
    · simp [input]
    · simp [look]
  unfold publicDataTail publicStrategyReturn publicFinishTail zlibTrailer
  simp only [M_bind_assoc]
  simp only [bind_app, pure_app, rdD_eq, hs, status,
    show (BUSY_STATE == GZIP_STATE) = false from by decide,
    show (BUSY_STATE == EXTRA_STATE) = false from by decide,
    show (BUSY_STATE == NAME_STATE) = false from by decide,
    show (BUSY_STATE == COMMENT_STATE) = false from by decide,
    show (BUSY_STATE == HCRC_STATE) = false from by decide,
    Bool.false_eq_true, ite_false, ldDeflateState_tab hs, zrd_eq, hz,
    show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl, Bool.false_and, Bool.or_false, activeBool, ite_true,
    strategy, show (d.level == 0) = false from beq_eq_false_iff_ne.mpr nonzero,
    show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
    show ((0 : Int32) == Z_RLE) = false from rfl, cfg, selected]


end Zlib.Deflate.Engine.Proofs
