import ZlibF.Proof.«deflate.c.engine.public-strategy-source»

/-! # Actual default NO_FLUSH dispatch and need_more return source -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 2500000 in
/-- Actual active default NO_FLUSH data dispatch reaches the slow strategy. -/
theorem public_busy_no_flush_slow_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0) :
    publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
      (do let bstate ← deflate_slow (some (.tab ds)) Z_NO_FLUSH
          publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH bstate) h := by
  have cfg : config_at (6 : Int32) = pure (⟨8, 16, 128, 128, .slow⟩ : Config) := by rfl
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
    level, strategy, show ((6 : Int32) == 0) = false from rfl,
    show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
    show ((0 : Int32) == Z_RLE) = false from rfl, cfg]

/-- The actual need_more return has the same retry marker for every flag. -/
theorem public_need_more_return {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) (flush : Int32) :
    publicStrategyReturn (some r) (some (.tab ds)) flush need_more h =
      .ok (Z_OK, if z.avail_out == 0 then setD h ds { d with last_flush := -1 } else h) := by
  unfold publicStrategyReturn
  simp only [bind_app, pure_app, zrd_eq, hz,
    show (need_more == finish_started) = false from rfl,
    show (need_more == finish_done) = false from rfl,
    show (need_more == need_more) = true from rfl,
    Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true]
  by_cases empty : z.avail_out = 0
  · simp only [empty, BEq.rfl, ite_true, bind_app, wrD_eq, hs, pure_app]
  · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false, bind_app, pure_app]

end Zlib.Deflate.Engine.Proofs
