import ZlibF.Proof.«deflate.c.engine.public-strategy-source»

/-! # Exact public dispatch and the BLOCK return path -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- BUSY default dispatch executes the actual slow strategy for every
nonzero request. The public entry must check the flag before this cutpoint. -/
theorem public_busy_positive_slow_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) :
    publicDataTail (some r) (some (.tab ds)) flush h =
      (do let bstate ← deflate_slow (some (.tab ds)) flush
          publicStrategyReturn (some r) (some (.tab ds)) flush bstate) h := by
  have cfg : config_at (6 : Int32) = pure (⟨8, 16, 128, 128, .slow⟩ : Config) := by rfl
  unfold publicDataTail publicStrategyReturn publicFinishTail zlibTrailer
  simp only [M_bind_assoc]
  simp only [bind_app, pure_app, rdD_eq, hs, status,
    show (BUSY_STATE == GZIP_STATE) = false from by decide,
    show (BUSY_STATE == EXTRA_STATE) = false from by decide,
    show (BUSY_STATE == NAME_STATE) = false from by decide,
    show (BUSY_STATE == COMMENT_STATE) = false from by decide,
    show (BUSY_STATE == HCRC_STATE) = false from by decide,
    Bool.false_eq_true, ite_false, ldDeflateState_tab hs,
    zrd_eq, hz, bne_iff_ne.mpr nonzero,
    show (BUSY_STATE != FINISH_STATE) = true from rfl,
    Bool.true_and, Bool.or_true, ite_true,
    level, strategy, show ((6 : Int32) == 0) = false from rfl,
    show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
    show ((0 : Int32) == Z_RLE) = false from rfl, cfg]

/-- The actual early return is independent of the flush argument. -/
theorem public_strategy_need_more_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) (empty : z.avail_out = 0) (flush : Int32) :
    publicStrategyReturn (some r) (some (.tab ds)) flush need_more h =
      .ok (Z_OK, setD h ds { d with last_flush := -1 }) := by
  unfold publicStrategyReturn
  simp only [bind_app, pure_app, zrd_eq, hz, empty, BEq.rfl, Bool.false_or, Bool.true_or,
    show (need_more == finish_started) = false from rfl,
    show (need_more == finish_done) = false from rfl,
    Bool.false_eq_true, ite_false, ite_true, wrD_eq, hs]

/-- BLOCK emits no extra marker. With a ready empty pending buffer,
publication is the actual no-op, including at zero caller capacity. -/
theorem public_strategy_block_done_ready {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (ready : PublishReady d) :
    publicStrategyReturn (some r) (some (.tab ds)) Z_BLOCK block_done h =
      .ok (Z_OK, if z.avail_out == 0 then setD h ds { d with last_flush := -1 } else h) := by
  have zero : pendingLen d.pending z.avail_out = 0 := by simp [pendingLen, ready.1]
  have publish := flush_pending_low_zero good.live.hz good.live.zst good.live.hs ready.2.2 zero
  unfold publicStrategyReturn publicFinishTail
  simp only [show (block_done == finish_started) = false from rfl,
    show (block_done == finish_done) = false from rfl,
    show (block_done == need_more) = false from rfl,
    show (Z_BLOCK == Z_PARTIAL_FLUSH) = false from rfl,
    show (Z_BLOCK != Z_BLOCK) = false from rfl,
    show (Z_BLOCK != Z_FINISH) = true from rfl,
    Bool.false_or, Bool.false_eq_true, beq_self_eq_true, ite_false, ite_true,
    bind_app, publish, zrd_eq, good.live.hz]
  by_cases empty : (z.avail_out == 0) = true <;>
    simp [empty, wrD_eq, good.live.hs, pure_app]

end Zlib.Deflate.Engine.Proofs
