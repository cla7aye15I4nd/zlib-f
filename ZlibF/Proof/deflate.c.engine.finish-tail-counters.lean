import ZlibF.Proof.«deflate.c.engine.flush-macro-counters»
import ZlibF.Proof.«deflate.c.engine.eof-controls»

/-! # Final literal settlement and block output have exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The final control tail reads fields after publishing; it retains exact totals. -/
theorem finish_tail_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.total_in = z.total_in ∧ returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨amount, other, otherZ, otherD, controlRun, boundaryA, _buffersA, accountA, _clearA, frameA, _lowA, _phaseA⟩ :=
    flush_final_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available wrap
  have effects := flush_control_run_counter_effects boundary buffers positive pointer cursor memory pending bits clear available true
    controlRun boundaryA.good.live.hz accountA
  have actualRun : finish_tail (some (.tab ds)) Z_FINISH h =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold finish_tail
    simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
    by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
  have same := actual_run_stream_unique actualRun run boundaryA.good.live.hz live
  rw [same] at accountA effects
  have count : produced = amount := (stream_accounting_counts_unique account accountA).2
  exact count ▸ effects

/-- EOF literal settlement and insertion reset preserve the real stream totals. -/
theorem slow_eof_finish_counter_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ produced ret after z' result, slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, _settledStart, _settledCount, settledClear, settledConfig, settledFrame, _symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  obtain ⟨insertRun, insertedBoundary, _insertedFrontier, insertedConfig⟩ :=
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
  refine ⟨produced, if z'.avail_out == 0 then finish_started else finish_done, after, z', result,
    ?_, boundaryA.good, accountA, effects⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun

end Zlib.Deflate.Engine.Proofs
