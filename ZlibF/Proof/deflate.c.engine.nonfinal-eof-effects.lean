import ZlibF.Proof.«deflate.c.engine.nonfinal-tail-effects»

/-! # Exact effects of the complete actual nonfinal EOF tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual literal settlement, insertion reset and optional block output
have exact wrapping totals, output interval and heap/allocation frame. -/
theorem slow_eof_nonfinal_effect_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result, slowEofTail (some (.tab ds)) flush h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
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
  obtain ⟨produced, ret, after, z', result, tailRun, boundaryA, _buffersA, accountA, _clearA, _configA,
      _lookA, _startA, _availableA, _insertA, _lowA, _phaseA, _returns, _exhausted⟩ :=
    finish_tail_nonfinal_boundary insertedBoundary insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      flush nonfinal
  have effects := finish_tail_nonfinal_run_effects insertedBoundary insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    flush nonfinal tailRun boundaryA.good.live.hz accountA
  obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ := slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun
  have shapeI := shape_setD settledBoundary.good.live.hs inserted
  have frameI : Frame settledHeap (setD settledHeap ds inserted)
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
    full_frame_weaken (state_store_full_frame settledHeap ds _) (fun _ same => Or.inr (Or.inl (Or.inl same)))
  obtain ⟨shapeT, frameT, _liveT, allocT, nextT⟩ := effects.2.2.2
  have settleEffect : RawOutputInterval h settledHeap ob oo 0 :=
    .of_private_frame boundary.good buffers pointer frameS
  have insertEffect : RawOutputInterval settledHeap (setD settledHeap ds inserted) ob oo 0 := .of_same rfl
  have settledEffect : RawOutputInterval h (setD settledHeap ds inserted) ob oo 0 := by
    simpa only [Nat.add_zero] using settleEffect.trans insertEffect
  have interval : RawOutputInterval h after ob oo produced := by
    simpa only [Nat.zero_add] using settledEffect.trans effects.2.2.1
  rw [configI.owned (ds := ds)] at frameT
  have shape := (shapeS.trans shapeI).trans shapeT
  have frame := full_frame_trans_shape
    (full_frame_trans_shape (full_private_frame_add_output frameS) frameI shapeS) frameT (shapeS.trans shapeI)
  have storage : Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk :=
    ⟨shape, frame, full_shape_live_change shape, allocT.trans allocS, nextT.trans nextS⟩
  refine ⟨produced, ret, after, z', result,
    ?_, boundaryA.good, accountA, effects.1, effects.2.1, interval, storage⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun

end Zlib.Deflate.Engine.Proofs
