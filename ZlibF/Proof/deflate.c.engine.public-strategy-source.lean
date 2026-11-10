import ZlibF.Proof.«deflate.c.engine.public-finish»
import ZlibF.Proof.«deflate.c.engine.finish-zero»

/-! # Exact public return statements following the default FINISH strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees («_tr_stored_block» «_tr_align»)
set_option autoImplicit false

/-- The exact source statements after strategy dispatch, including the
other block-state branches. The trailer remains the actual public tail. -/
def publicStrategyReturn (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32)
    (bstate : block_state) : M Int32 := do
  -- if (bstate == finish_started || bstate == finish_done) s->status = FINISH_STATE;
  if bstate == finish_started || bstate == finish_done then
    wr s (fun d => { d with status := FINISH_STATE })
  -- if (bstate == need_more || bstate == finish_started) { if (strm->avail_out == 0) s->last_flush = -1; return Z_OK; }
  if bstate == need_more || bstate == finish_started then
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  if bstate == block_done then
    if flush == Z_PARTIAL_FLUSH then
      _tr_align s
    else if flush != Z_BLOCK then
      -- FULL_FLUSH or SYNC_FLUSH
      _tr_stored_block s (Ptr.null : BPtr) 0 0
      if flush == Z_FULL_FLUSH then
        CLEAR_HASH s                                        -- forget history
        if (← rd s (·.lookahead)) == 0 then
          wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })
    flush_pending strm
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  publicFinishTail strm s flush

set_option maxHeartbeats 2500000 in
/-- With the default strategy and BUSY status, the actual FINISH data
source always dispatches to the slow engine. This is a source equality;
it makes no assumption about successful engine execution. -/
theorem public_busy_finish_slow_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0) :
    publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      (do let bstate ← deflate_slow (some (.tab ds)) Z_FINISH
          publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH bstate) h := by
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
    zrd_eq, hz, show (Z_FINISH != Z_NO_FLUSH) = true from rfl,
    show (BUSY_STATE != FINISH_STATE) = true from rfl,
    Bool.true_and, Bool.or_true, ite_true,
    level, strategy, show ((6 : Int32) == 0) = false from rfl,
    show ((0 : Int32) == Z_HUFFMAN_ONLY) = false from rfl,
    show ((0 : Int32) == Z_RLE) = false from rfl, cfg]

end Zlib.Deflate.Engine.Proofs
