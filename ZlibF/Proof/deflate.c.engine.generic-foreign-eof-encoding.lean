import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-tail»
import ZlibF.Proof.«deflate.c.engine.eof-tail-encoding»
import ZlibF.Proof.«deflate.c.engine.finish-tail-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual foreign-output EOF tail settles the literal, resets insertion, and emits
the real final block in source order, retaining exact independent encoding and BufferFrame. -/
theorem default_foreign_slow_eof_finish_tail_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState) (ys : List Symbol)
      (before : List Bool) (written : List UInt8) (remaining : List Bool)
      (kind : Nat) (body padding : List Bool),
      slowEofTail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧ result.lookahead = 0 ∧
      result.strstart = d.strstart ∧ result.match_available = 0 ∧
      result.insert.toNat = min d.strstart.toNat 2 ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) ∧
      result.bi_valid.toInt.toNat = 0 ∧ PendingBits h d before ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ padding.length < 8 ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 1 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      (∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (origin + d.strstart.toNat))) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, settledStart, _settledCount, settledClear, settledConfig, settledFrame, symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  let hi := setD settledHeap ds inserted
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
  obtain ⟨produced, after, z', result, beforeI, written, remaining, kind, body, padding,
    tailRun, boundaryA, buffersA, accountA, clearA, frameA, finalA, pendingI, bytesA, pendingA,
    kindA, padBound, storedPad, wire, grammar,lowA,phaseA,frameTail⟩ :=
    default_foreign_finish_tail_final_content_encoding insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap]; exact wrap)
  have realRun : slowEofTail (some (.tab ds)) Z_FINISH h =
      .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) := by
    unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := boundary.symbols
  have pendingBefore := pending_bits_base trees cursor
  have zeroI : inserted.pending = 0 := by change settled.pending = 0; rw [settledFrame]; exact pending
  have sameHeld : Zlib.Trees.Proofs.Out.natBits inserted.bi_buf.toNat inserted.bi_valid.toInt.toNat =
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
    change Zlib.Trees.Proofs.Out.natBits settled.bi_buf.toNat settled.bi_valid.toInt.toNat = _
    rw [settledFrame]
  have beforeEq : beforeI = Zlib.Trees.Proofs.Out.outBits buf d :=
    ((pending_bits_zero_value zeroI pendingI).trans sameHeld).trans
      (pending_bits_zero_value pending pendingBefore).symm
  rw [beforeEq] at wire
  have endBase : base + represented ys = origin + d.strstart.toNat := by
    have count := settledBoundary.accounted
    simpa only [pendingCredit, settledFlag, ite_true, Nat.add_zero, settledStart] using count
  rw [endBase] at grammar
  obtain ⟨shapeS,frameS,_liveS,_allocS,_nextS⟩ := slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun
  have frameI : Frame settledHeap hi (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame settledHeap ds inserted) (fun _ same => Or.inr (Or.inl same))
  have frameSI := full_frame_trans_shape frameS frameI shapeS
  have shapeSI := shapeS.trans (shape_setD settledBoundary.good.live.hs inserted)
  have outputView := private_frame_foreign_output_same boundary.good buffers pointer frameSI
  have keys : ∀ b,DeflateOwned ds inserted b ↔ DeflateOwned ds d b := by
    intro b
    change DeflateOwned ds settled b ↔ DeflateOwned ds d b
    rw [settledFrame]
    rfl
  have frameTailOld : BufferFrame hi after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨.ref (.dstate_depth owner) oo,produced⟩] := by
    change BufferFrame hi after (fun b => StreamRoot r b ∨ DeflateOwned ds inserted b) [⟨z.next_out,produced⟩] at frameTail
    simpa only [keys,pointer] using frameTail
  have fullFrame := foreign_buffer_frame_precompose frameSI shapeSI outputView frameTailOld
  have finalConfig : ConfigFrame inserted result := by rw [frameA]; rfl
  refine ⟨produced, after, z', result, ys, Zlib.Trees.Proofs.Out.outBits buf d,
    written, remaining, kind, body, padding, realRun, boundaryA, buffersA, accountA, clearA,
    configI.trans finalConfig, ?_, ?_, ?_, ?_, lowA, phaseA, symbols, finalA, pendingBefore, bytesA, pendingA,
    kindA, padBound, storedPad, wire, grammar,by simpa only [pointer] using fullFrame⟩
  · rw [frameA]; exact settledLook
  · rw [frameA]; exact settledStart
  · rw [frameA]; exact settledFlag
  · rw [frameA]
    change (eofInsert settled).insert.toNat = min d.strstart.toNat 2
    rw [eof_insert_count, settledStart]

end Zlib.Deflate.Engine.Proofs
