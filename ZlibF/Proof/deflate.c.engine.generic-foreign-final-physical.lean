import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-physical»
import ZlibF.Proof.«deflate.c.engine.finish-tail-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual final block publication and its source return tests retain the complete private/output frame. -/
theorem default_foreign_finish_tail_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_amount, other, otherZ, otherD, _before, _written, _remaining, _kind, _body, _padding,
    macroRun, boundaryA, _frontierA, _buffersA, _accountA, _clearA, frameA, _lowA, _phaseA, _cursorA, _rest⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available true
  have run1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h=.ok ((),other) := macroRun
  have wrapA : otherD.wrap=1 := by rw [frameA]; exact wrap
  have controlRun : FLUSH_BLOCK (some (.tab ds)) 1 h=
      .ok ((if otherZ.avail_out==0 then some finish_started else none),other) := by
    unfold FLUSH_BLOCK
    simp only [bind_app,run1,ldDeflateState_tab boundaryA.good.live.hs,boundaryA.good.live.back,zrd_eq,boundaryA.good.live.hz]
    by_cases empty : (otherZ.avail_out==0)=true <;> simp [empty,pure_app,wrapA]
  have storage := default_foreign_flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available true controlRun
  have tested : finish_tail (some (.tab ds)) Z_FINISH h =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold finish_tail
    simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
    by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact storage

/-- The complete actual EOF tail settles the final literal, resets insertion, publishes the final block and retains the full object/allocation frame. -/
theorem default_foreign_slow_eof_finish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ produced ret after z' result, slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, _settledStart, _settledCount, settledClear, settledConfig, settledFrame, _symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  obtain ⟨insertRun, insertedBoundary, insertedFrontier, insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds inserted)
    (fun k equal => (stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have configI : ConfigFrame d inserted := settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear inserted := ⟨settledClear.bl, settledClear.opt, settledClear.fixed⟩
  have bitsI : inserted.bi_valid.toInt ≤ 7 := by
    change settled.bi_valid.toInt ≤ 7
    have bitFrame : settled.bi_valid = d.bi_valid := by rw [settledFrame]
    rw [bitFrame]
    have low := boundary.bits
    omega
  obtain ⟨produced, after, z', result, _before, _written, _remaining, _kind, _body, _padding,
    tailRun, boundaryA, _buffersA, accountA, _clearA, frameA, _finalA, _rest⟩ :=
    default_foreign_finish_tail_final_content_encoding insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap]; exact wrap)
  obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ := slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun
  have shapeI := shape_setD settledBoundary.good.live.hs inserted
  have frameI : Frame settledHeap (setD settledHeap ds inserted)
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) :=
    full_frame_weaken (state_store_full_frame settledHeap ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
  obtain ⟨shapeT, frameT, _liveT, allocT, nextT⟩ := default_foreign_finish_tail_run_full_storage insertedBoundary insertedFrontier insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    (by rw [configI.wrap]; exact wrap) tailRun
  rw [configI.owned (ds := ds)] at frameT
  have shape := (shapeS.trans shapeI).trans shapeT
  have frame := full_frame_trans_shape
    (full_frame_trans_shape (full_private_frame_add_output frameS) frameI shapeS) frameT (shapeS.trans shapeI)
  have storage : Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk :=
    ⟨shape, frame, full_shape_live_change shape, allocT.trans allocS, nextT.trans nextS⟩
  refine ⟨produced, if z'.avail_out == 0 then finish_started else finish_done, after, z', result,
    ?_, boundaryA.good, accountA, storage⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun


/-- Every presentation of the real EOF return has the same complete physical frame. -/
theorem default_foreign_slow_eof_finish_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_produced,_ret,other,_z',_result,tested,_good,_account,storage⟩ :=
    default_foreign_slow_eof_finish_full_storage_execution boundary frontier buffers empty positive pointer cursor memory pending wrap
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  exact heaps ▸ storage

end Zlib.Deflate.Engine.Proofs
