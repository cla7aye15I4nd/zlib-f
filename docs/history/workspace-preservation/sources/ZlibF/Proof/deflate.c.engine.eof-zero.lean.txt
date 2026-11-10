import ZlibF.Proof.«deflate.c.engine.final-zero»

/-! # Zero-bit result of the complete actual EOF tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual EOF literal and insertion prefix reaches the zero-bit
final publication. This also retains the empty-lookahead conclusion. -/
theorem slow_eof_finish_zero_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ ret after z' result, slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ result.lookahead = 0 ∧ result.bi_valid.toInt = 0 := by
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
  obtain ⟨produced, after, z', result, tailRun, boundaryA, _buffersA, _accountA, _clearA, frameA, _lowA, _phaseA⟩ :=
    finish_tail_final_boundary insertedBoundary insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap]; exact wrap)
  have zero := finish_tail_run_zero insertedBoundary insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    (by rw [configI.wrap]; exact wrap) tailRun boundaryA.good.live.hs
  refine ⟨if z'.avail_out == 0 then finish_started else finish_done, after, z', result, ?_, boundaryA.good, ?_, zero⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  · rw [frameA]
    exact settledLook

/-- The lookahead and zero-bit facts hold on the established actual EOF
return heap, by determinism of that same translated call. -/
theorem slow_eof_finish_run_zero {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : after.dstates ds = some result) :
    result.lookahead = 0 ∧ result.bi_valid.toInt = 0 := by
  obtain ⟨otherRet, other, otherZ, otherD, otherRun, otherGood, look, zero⟩ :=
    slow_eof_finish_zero_execution boundary frontier buffers empty positive pointer cursor memory pending wrap
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood
  have states : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← states]
  exact ⟨look, zero⟩

end Zlib.Deflate.Engine.Proofs
