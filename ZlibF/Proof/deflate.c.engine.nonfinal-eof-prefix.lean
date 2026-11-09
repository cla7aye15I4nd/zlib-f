import ZlibF.Proof.«deflate.c.engine.nonfinal-tail-prefix»
import ZlibF.Proof.«deflate.c.engine.eof-tail»
import ZlibF.Proof.«deflate.c.engine.strategy-encoding-cut»

/-! # Actual nonfinal EOF settlement composes with the independent prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Actual nonfinal EOF settlement, insertion reset and optional block
publication connect the original held bits to the accepted EOF input.
Empty symbol buffers skip block emission; every output capacity is
included. The later public marker is a separate translated operation. -/
theorem slow_eof_nonfinal_block_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result ys before written remaining blockBits,
      slowEofTail (some (.tab ds)) flush h = .ok (ret, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      ConfigFrame d result ∧ result.lookahead = 0 ∧ result.strstart = d.strstart ∧
      result.match_available = 0 ∧ result.insert.toNat = min d.strstart.toNat 2 ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
      BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix input (origin + d.strstart.toNat)) ∧
      (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8 ∧
      (ret = need_more ∨ ret = block_done) ∧ (ret = need_more → z'.avail_out = 0) := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, settledStart, _settledCount, settledClear, settledConfig, settledFrame, symbols⟩ :=
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
  have positionI : offset % 8 = inserted.bi_valid.toInt.toNat % 8 := by
    change offset % 8 = settled.bi_valid.toInt.toNat % 8
    rw [settledFrame]
    exact position
  obtain ⟨produced, ret, after, z', result, beforeI, written, remaining, blockBits,
      tailRun, stateA, endA, buffersA, accountA, clearA, configA, lookA, startA, flagA,
      insertA, lowA, readyA, pendingI, bytesA, pendingA, wireA, meaningA, positionA, returns, exhausted⟩ :=
    finish_tail_nonfinal_block_prefix insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag positionI flush nonfinal
  obtain ⟨_pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
  have pendingBefore := pending_bits_base trees cursor
  have zeroI : inserted.pending = 0 := by change settled.pending = 0; rw [settledFrame]; exact pending
  have sameHeld : Zlib.Trees.Proofs.Out.natBits inserted.bi_buf.toNat inserted.bi_valid.toInt.toNat =
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
    change Zlib.Trees.Proofs.Out.natBits settled.bi_buf.toNat settled.bi_valid.toInt.toNat = _
    rw [settledFrame]
  have beforeEq : beforeI = Zlib.Trees.Proofs.Out.outBits buf d :=
    ((pending_bits_zero_value zeroI pendingI).trans sameHeld).trans
      (pending_bits_zero_value pending pendingBefore).symm
  rw [beforeEq] at wireA
  have endBase : base + represented ys = origin + d.strstart.toNat := by
    have count := settledBoundary.accounted
    simpa only [pendingCredit, settledFlag, ite_true, Nat.add_zero, settledStart] using count
  rw [endBase] at meaningA
  refine ⟨produced, ret, after, z', result, ys, Zlib.Trees.Proofs.Out.outBits buf d,
    written, remaining, blockBits, ?_, stateA, endA, buffersA, accountA, clearA,
    configI.trans configA, ?_, ?_, flagA, ?_, lowA, readyA, symbols, pendingBefore,
    bytesA, pendingA, wireA, meaningA, positionA, returns, exhausted⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  · rw [lookA]; exact settledLook
  · rw [startA]; exact settledStart
  · rw [insertA]
    change (eofInsert settled).insert.toNat = min d.strstart.toNat 2
    rw [eof_insert_count, settledStart]

end Zlib.Deflate.Engine.Proofs
