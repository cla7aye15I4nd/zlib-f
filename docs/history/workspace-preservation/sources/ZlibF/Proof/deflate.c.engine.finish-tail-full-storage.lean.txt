import ZlibF.Proof.«deflate.c.engine.loop-full-storage»
import ZlibF.Proof.«deflate.c.engine.finish-tail-counters»

/-! # Complete ordinary strategy heap frames -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual final deferred-literal prefix changes only the private
pending-byte buffer and state record, with no allocation or object loss. -/
theorem slow_eof_literal_run_full_storage {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (run : slowEofLiteral (some (.tab ds)) h = .ok ((), after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases available : d.match_available = 0
  · have tested : slowEofLiteral (some (.tab ds)) h = .ok ((), h) := by
      unfold slowEofLiteral
      simp only [bind_app, ldDeflateState_tab boundary.good.live.hs, available,
        bne_self_eq_false, Bool.false_eq_true, ite_false, pure_app]
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    exact full_storage_refl h _
  · obtain ⟨w, wa, win, get, _view, _form⟩ := boundary.data
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
    let c := wa[d.strstart.toNat - 1]!
    let dt := literalState d c
    let packed := literalBytes buf d c
    let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
    let result := {dt with match_available := 0}
    let other := setD ht ds result
    have room := literal_room boundary.good.inv strict
    have stateT : ht.dstates ds = some dt := by simp [ht]
    obtain ⟨size, _⟩ := window_extent boundary.good win get
    have previousByte := boundary.deferred available
    have ranged := boundary.range
    have fit : d.strstart.toNat - 1 < wa.size := by dsimp only [fillEnd] at ranged; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [win, u32_sub_one previousByte]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) get (by omega)
    have tally : tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
      tally_literal_run trees.base c room
    have put : wr (some (.tab ds)) (fun d => {d with match_available := 0}) ht = .ok ((), other) := by
      simp only [wrD_eq, stateT]
      rfl
    have tested : slowEofLiteral (some (.tab ds)) h = .ok ((), other) := by
      unfold slowEofLiteral
      have has : (d.match_available != 0) = true := by simpa using available
      simp only [bind_app, ldDeflateState_tab boundary.good.live.hs, has, ite_true, read, tally]
      exact put
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    have tallyStorage : OutputStorage h ht r ds pb pb := output_bits_storage boundary.good.live.hs trees.base.bytes
    have shapeD := shape_setD stateT result
    have shape := tallyStorage.shape.trans shapeD
    have frameT : Frame h ht (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      apply full_frame_weaken tallyStorage.frame
      intro b changed
      rcases changed with root | state | same | same
      · exact Or.inl root
      · exact Or.inr (Or.inl state)
      · subst b; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
      · subst b; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    have frameD : Frame ht other (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
      full_frame_weaken (state_store_full_frame ht ds _) (fun _ same => Or.inr (Or.inl same))
    exact ⟨shape, full_frame_trans_shape frameT frameD tallyStorage.shape, full_shape_live_change shape, rfl, rfl⟩

/-- Actual final block publication and its source return tests retain the complete private/output frame. -/
theorem finish_tail_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_amount, other, otherZ, _otherD, controlRun, _boundaryA, _buffersA, _accountA, _clearA, _frameA, _lowA, _phaseA⟩ :=
    flush_final_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available wrap
  have storage := flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available true controlRun
  have tested : finish_tail (some (.tab ds)) Z_FINISH h =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold finish_tail
    simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
    by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact storage

/-- The complete actual EOF tail settles the final literal, resets insertion, publishes the final block and retains the full object/allocation frame. -/
theorem slow_eof_finish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ produced ret after z' result, slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, _settledStart, _settledCount, settledClear, settledConfig, settledFrame, _symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  obtain ⟨insertRun, insertedBoundary, _insertedFrontier, insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds inserted)
    (fun k equal => (stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z)
  have configI : ConfigFrame d inserted := settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear inserted := ⟨settledClear.bl, settledClear.opt, settledClear.fixed⟩
  have bitsI : inserted.bi_valid.toInt ≤ 7 := by
    change settled.bi_valid.toInt ≤ 7
    have bitFrame : settled.bi_valid = d.bi_valid := by rw [settledFrame]
    rw [bitFrame]
    have low := boundary.bits
    omega
  obtain ⟨produced, after, z', result, tailRun, boundaryA, _buffersA, accountA, _clearA, frameA, _lowA, _phaseA⟩ :=
    finish_tail_final_boundary insertedBoundary insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap]; exact wrap)
  have effects := finish_tail_run_counter_effects insertedBoundary insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    (by rw [configI.wrap]; exact wrap) tailRun boundaryA.good.live.hz accountA
  obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ := slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun
  have shapeI := shape_setD settledBoundary.good.live.hs inserted
  have frameI : Frame settledHeap (setD settledHeap ds inserted)
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
    full_frame_weaken (state_store_full_frame settledHeap ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
  obtain ⟨shapeT, frameT, _liveT, allocT, nextT⟩ := finish_tail_run_full_storage insertedBoundary insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    (by rw [configI.wrap]; exact wrap) tailRun
  rw [configI.owned (ds := ds)] at frameT
  have shape := (shapeS.trans shapeI).trans shapeT
  have frame := full_frame_trans_shape
    (full_frame_trans_shape (full_private_frame_add_output frameS) frameI shapeS) frameT (shapeS.trans shapeI)
  have storage : Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk :=
    ⟨shape, frame, full_shape_live_change shape, allocT.trans allocS, nextT.trans nextS⟩
  refine ⟨produced, if z'.avail_out == 0 then finish_started else finish_done, after, z', result,
    ?_, boundaryA.good, accountA, effects.1, effects.2, storage⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun

end Zlib.Deflate.Engine.Proofs
