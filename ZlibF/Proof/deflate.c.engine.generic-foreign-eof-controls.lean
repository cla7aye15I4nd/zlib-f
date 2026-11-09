import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-controls»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-tail»
import ZlibF.Proof.«deflate.c.engine.eof-tail»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real final tail retains both public controls and the empty cursor. -/
theorem default_foreign_finish_tail_run_controls {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out= .ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0) (wrap : d.wrap=1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h= .ok (ret,after)) (live : after.dstates ds=some result) :
    StrategyControls d result := by
  obtain ⟨produced,other,otherZ,otherD,_before,_written,_remaining,_kind,_body,_padding,
    macroRun,stateA,_endA,_buffersA,_accountA,_clearA,frameA,_lowA,_phaseA,cursorA,_rest⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available true
  have wrapA : otherD.wrap=1 := by rw [frameA];exact wrap
  have macroRun1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h= .ok ((),other) := macroRun
  have controlRun : FLUSH_BLOCK (some (.tab ds)) 1 h=
      .ok ((if otherZ.avail_out==0 then some finish_started else none),other) := by
    unfold FLUSH_BLOCK
    simp only [bind_app,macroRun1,ldDeflateState_tab stateA.good.live.hs,stateA.good.live.back,zrd_eq,stateA.good.live.hz]
    by_cases empty : (otherZ.avail_out==0)=true <;> simp [empty,pure_app,wrapA]
  have tested : finish_tail (some (.tab ds)) Z_FINISH h=
      .ok ((if otherZ.avail_out==0 then finish_started else finish_done),other) := by
    unfold finish_tail
    simp only [beq_self_eq_true,ite_true,bind_app,controlRun]
    by_cases empty : (otherZ.avail_out==0)=true <;> simp [empty,pure_app]
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [heaps] at stateA
  have states : otherD=result := Option.some.inj (stateA.good.live.hs.symm.trans live)
  rw [← states]
  exact ⟨cursorA,by rw [frameA],by rw [frameA]⟩

/-- Real EOF literal settlement, insert reset and final publication preserve status/last_flush. -/
theorem default_foreign_slow_eof_finish_run_controls {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0)
    (positive : 0<d.level.toInt) (pointer : z.next_out= .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out=d.pending_buf) (memory : d.lit_bufsize.toNat=16384)
    (pending : d.pending=0) (wrap : d.wrap=1)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h= .ok (ret,after)) (live : after.dstates ds=some result) :
    StrategyControls d result := by
  obtain ⟨settledHeap,settled,ys,settleRun,settledBoundary,settledFrontier,settledBuffers,
    settledFlag,settledLook,_settledStart,_settledCount,settledClear,settledConfig,settledFrame,_symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  obtain ⟨insertRun,insertedBoundary,insertedFrontier,insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds inserted)
    (fun k equal => (stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have configI : ConfigFrame d inserted := settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear inserted := ⟨settledClear.bl,settledClear.opt,settledClear.fixed⟩
  have bitsI : inserted.bi_valid.toInt≤7 := by
    change settled.bi_valid.toInt≤7
    have bitFrame : settled.bi_valid=d.bi_valid := by rw [settledFrame]
    rw [bitFrame]
    have low := boundary.bits
    omega
  have positiveI : 0<inserted.level.toInt := by rw [configI.level];exact positive
  have cursorI : inserted.pending_out=inserted.pending_buf := by
    change settled.pending_out=settled.pending_buf
    rw [settledFrame]
    exact cursor
  have memoryI : inserted.lit_bufsize.toNat=16384 := by rw [configI.memory];exact memory
  have pendingI : inserted.pending=0 := by change settled.pending=0;rw [settledFrame];exact pending
  have wrapI : inserted.wrap=1 := by rw [configI.wrap];exact wrap
  obtain ⟨produced,other,otherZ,otherD,_before,_written,_remaining,_kind,_body,_padding,
    tailRun,stateA,_buffersA,_accountA,_rest⟩ :=
    default_foreign_finish_tail_final_content_encoding insertedBoundary insertedFrontier insertedBuffers positiveI pointer cursorI
      memoryI pendingI bitsI clearI settledFlag wrapI
  have controls := default_foreign_finish_tail_run_controls insertedBoundary insertedFrontier insertedBuffers positiveI pointer cursorI
    memoryI pendingI bitsI clearI settledFlag wrapI tailRun stateA.good.live.hs
  have tested : slowEofTail (some (.tab ds)) Z_FINISH h=
      .ok ((if otherZ.avail_out==0 then finish_started else finish_done),other) := by
    unfold slowEofTail
    rw [bind_app,settleRun]
    simp only []
    rw [bind_app,insertRun]
    exact tailRun
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [heaps] at stateA
  have states : otherD=result := Option.some.inj (stateA.good.live.hs.symm.trans live)
  rw [← states]
  exact ⟨controls.empty_cursor,by rw [controls.status];change settled.status=d.status;rw [settledFrame],
    by rw [controls.last_flush];change settled.last_flush=d.last_flush;rw [settledFrame]⟩

end Zlib.Deflate.Engine.Proofs
