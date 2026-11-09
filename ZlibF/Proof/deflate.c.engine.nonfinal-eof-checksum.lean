import ZlibF.Proof.«deflate.c.engine.eof-checksum»
import ZlibF.Proof.«deflate.c.engine.nonfinal-eof-tail»

/-! # Nonfinal EOF settlement and optional block output preserve Adler -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual nonfinal EOF control retains Adler whether it skips an
empty symbol buffer or publishes its computed nonfinal block. -/
theorem finish_tail_nonfinal_run_adler {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH)
    (run : finish_tail (some (.tab ds)) flush h = .ok (ret, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.adler = z.adler := by
  by_cases empty : d.sym_next = 0
  · have actual : finish_tail (some (.tab ds)) flush h = .ok (block_done, h) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    have same := actual_run_stream_unique actual run boundary.good.live.hz live
    exact congrArg ZStream.adler same.symm
  · obtain ⟨_amount, _other, otherZ, _otherD, controlRun, stateA, _buffersA, accountA,
        _clearA, _frameA, _lowA, _readyA⟩ :=
      flush_nonfinal_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available
    have adler := flush_control_run_adler boundary buffers positive pointer cursor memory pending bits clear available false
      controlRun stateA.good.live.hz accountA
    have actual : finish_tail (some (.tab ds)) flush h =
        .ok ((if otherZ.avail_out == 0 then need_more else block_done), _other) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, controlRun]
      by_cases exhausted : (otherZ.avail_out == 0) = true <;> simp [exhausted, pure_app]
    have same := actual_run_stream_unique actual run stateA.good.live.hz live
    exact same ▸ adler

/-- The actual complete nonfinal EOF tail preserves Adler through literal
settlement, insertion reset, optional block emission and pending copy. -/
theorem slow_eof_nonfinal_adler_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result, slowEofTail (some (.tab ds)) flush h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧ z'.adler = z.adler := by
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
  obtain ⟨produced, ret, after, z', result, tailRun, stateA, _buffersA, accountA, _clearA, _configA,
      _lookA, _startA, _flagA, _insertA, _lowA, _readyA, _returnsA, _exhaustedA⟩ :=
    finish_tail_nonfinal_boundary insertedBoundary insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag flush nonfinal
  have adler := finish_tail_nonfinal_run_adler insertedBoundary insertedBuffers
    (by rw [configI.level]; exact positive) pointer
    (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
    (by rw [configI.memory]; exact memory)
    (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
    flush nonfinal tailRun stateA.good.live.hz accountA
  refine ⟨produced, ret, after, z', result, ?_, stateA.good, accountA, adler⟩
  unfold slowEofTail
  rw [bind_app, settleRun]
  simp only []
  rw [bind_app, insertRun]
  exact tailRun

/-- Any presentation of the same actual nonfinal EOF return has the
same retained checksum; no successful callee contract is assumed. -/
theorem slow_eof_nonfinal_run_adler {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH)
    (run : slowEofTail (some (.tab ds)) flush h = .ok (ret, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.adler = z.adler := by
  obtain ⟨_produced, _ret, _other, _otherZ, _otherD, actual, goodA, _accountA, adler⟩ :=
    slow_eof_nonfinal_adler_execution boundary frontier buffers empty positive pointer cursor memory pending flush nonfinal
  have same := actual_run_stream_unique actual run goodA.live.hz live
  exact same ▸ adler

end Zlib.Deflate.Engine.Proofs
