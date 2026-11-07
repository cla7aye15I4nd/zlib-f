import ZlibF.Proof.«deflate.c.engine.eof-literal»
import ZlibF.Proof.«deflate.c.engine.final-control»

/-! # The complete actual slow EOF tail under Z_FINISH -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The source tail after the loop exits without an early block return. -/
def slowEofTail (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  slowEofLiteral s
  wr s eofInsert
  finish_tail s flush

/-- The complete translated slow function reaches exactly this tail. -/
theorem deflate_slow_eof_tail_source (s : DeflateStatePtr) (flush : Int32) :
    deflate_slow s flush = (do
      let st ← cwhile forever (deflate_slow_body s flush) {}
      if let some r := st.ret then return r
      slowEofTail s flush) := by
  rw [deflate_slow_eof_source]
  rfl

/-- At actual EOF the final deferred literal, pending-key reset and final
block publication all execute in source order. Zero/short output room is
included. This is the tail cutpoint; the preceding FINISH loop is still
a separate obligation. -/
theorem slow_eof_finish_tail {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState) (ys : List Symbol),
      slowEofTail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧ result.lookahead = 0 ∧
      result.strstart = d.strstart ∧ result.match_available = 0 ∧
      result.insert.toNat = min d.strstart.toNat 2 ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, settledStart, _settledCount, settledClear, settledConfig, settledFrame, symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  let hi := setD settledHeap ds inserted
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
  obtain ⟨produced, after, z', result, tailRun, boundaryA, buffersA, accountA, clearA, frameA, lowA, phaseA⟩ :=
    finish_tail_final_boundary insertedBoundary insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap]; exact wrap)
  have finalConfig : ConfigFrame inserted result := by rw [frameA]; rfl
  refine ⟨produced, after, z', result, ys, ?_, boundaryA, buffersA, accountA, clearA,
    configI.trans finalConfig, ?_, ?_, ?_, ?_, lowA, phaseA, symbols⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  · rw [frameA]; exact settledLook
  · rw [frameA]; exact settledStart
  · rw [frameA]; exact settledFlag
  · rw [frameA]
    change (eofInsert settled).insert.toNat = min d.strstart.toNat 2
    rw [eof_insert_count, settledStart]

end Zlib.Deflate.Engine.Proofs
