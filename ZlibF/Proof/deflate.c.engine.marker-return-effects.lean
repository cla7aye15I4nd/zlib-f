import ZlibF.Proof.«deflate.c.engine.partial-sync-effects»
import ZlibF.Proof.«deflate.c.engine.full-flush-effects»
import ZlibF.Proof.«deflate.c.engine.partial-sync-return»
import ZlibF.Proof.«deflate.c.engine.full-flush-return»

/-! # Every actual marker return includes exact retry-store effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- All three actual flushing marker returns retain exact wrapping totals,
output interval, whole-object frame and allocation ledgers. The actual
completed strategy establishes the empty symbols and settled EOF premises. -/
theorem public_strategy_marker_done_effects {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) :
    ∃ produced after z' result,
      publicStrategyReturn (some r) (some (.tab ds)) flush block_done h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let workPrefix : M Unit := if flush == Z_FULL_FLUSH then (do
      Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
      let _ ← (do
        CLEAR_HASH (some (.tab ds))
        if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
          wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
      flush_pending (some r)) else (do
      let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
        else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0)
      flush_pending (some r))
  have source : publicStrategyReturn (some r) (some (.tab ds)) flush block_done = (do
      let _ ← workPrefix
      if (← zrd (some r) (·.avail_out)) == 0 then
        wr (some (.tab ds)) (fun d => { d with last_flush := -1 })
        return Z_OK
      return Z_OK) := by
    rcases flag with partialFlag | sync | full
    · subst flush
      simpa only [workPrefix, show (Z_PARTIAL_FLUSH == Z_FULL_FLUSH) = false from rfl,
        Bool.false_eq_true, ite_false] using public_strategy_partial_sync_source (some r) (some (.tab ds)) Z_PARTIAL_FLUSH (Or.inl rfl)
    · subst flush
      simpa only [workPrefix, show (Z_SYNC_FLUSH == Z_FULL_FLUSH) = false from rfl,
        Bool.false_eq_true, ite_false] using public_strategy_partial_sync_source (some r) (some (.tab ds)) Z_SYNC_FLUSH (Or.inr rfl)
    · subst flush
      simpa only [workPrefix, BEq.rfl, ite_true] using public_strategy_full_source (some r) (some (.tab ds))
  have prefixEffects : ∃ produced after z' result,
      workPrefix h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
    rcases flag with partialFlag | sync | full
    · subst flush
      simpa only [workPrefix, show (Z_PARTIAL_FLUSH == Z_FULL_FLUSH) = false from rfl,
        Bool.false_eq_true, ite_false] using
        partial_sync_publication_effects boundary.good trees buffers pointer publish Z_PARTIAL_FLUSH (Or.inl rfl)
    · subst flush
      simpa only [workPrefix, show (Z_SYNC_FLUSH == Z_FULL_FLUSH) = false from rfl,
        Bool.false_eq_true, ite_false] using
        partial_sync_publication_effects boundary.good trees buffers pointer publish Z_SYNC_FLUSH (Or.inr rfl)
    · subst flush
      simpa only [workPrefix, BEq.rfl, ite_true] using
        full_publication_effects boundary buffers trees pointer publish look available
  obtain ⟨produced, middle, z', result, run, goodM, buffersM, account, inputM, outputM,
      intervalM, shapeM, frameM, liveM, allocM, nextM⟩ := prefixEffects
  have returned : publicStrategyReturn (some r) (some (.tab ds)) flush block_done h =
      (if z'.avail_out == 0 then .ok (Z_OK, setD middle ds { result with last_flush := -1 })
        else .ok (Z_OK, middle)) := by
    rw [source, bind_app, run]
    simp only [bind_app, zrd_eq, goodM.live.hz]
    split <;> simp only [wrD_eq, goodM.live.hs, bind_app, pure_app]
  by_cases exhausted : (z'.avail_out == 0) = true
  · have shapeD := shape_setD goodM.live.hs { result with last_flush := -1 }
    have frameD : Frame middle (setD middle ds { result with last_flush := -1 })
        (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
      full_frame_weaken (state_store_full_frame middle ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
    have intervalD : RawOutputInterval middle (setD middle ds { result with last_flush := -1 }) ob (oo + produced) 0 := .of_same rfl
    have shape := shapeM.trans shapeD
    exact ⟨produced, _, z', _, by simpa only [exhausted, ite_true] using returned,
      last_flush_good goodM (-1), last_flush_buffers goodM buffersM (-1), account, inputM, outputM,
      by simpa only [Nat.add_zero] using intervalM.trans intervalD, shape,
      full_frame_trans_shape frameM frameD shapeM, full_shape_live_change shape, allocM, nextM⟩
  · exact ⟨produced, middle, z', result, by simpa only [exhausted, Bool.false_eq_true, ite_false] using returned,
      goodM, buffersM, account, inputM, outputM, intervalM, shapeM, frameM, liveM, allocM, nextM⟩

end Zlib.Deflate.Engine.Proofs
