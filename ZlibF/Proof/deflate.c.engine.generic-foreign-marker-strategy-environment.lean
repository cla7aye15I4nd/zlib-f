import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-call»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-final-physical»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- After settling the deferred literal, a non-FINISH tail flushes exactly
when symbols remain. An empty symbol buffer returns block_done even at
zero output capacity. No final block or public marker is added here. -/
theorem foreign_finish_tail_nonfinal_static_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ produced ret after z' result,
      finish_tail (some (.tab ds)) flush h = .ok (ret, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      ConfigFrame d result ∧ result.lookahead = d.lookahead ∧ result.strstart = d.strstart ∧
      result.match_available = 0 ∧ result.insert = d.insert ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ret = need_more ∨ ret = block_done) ∧ (ret = need_more → z'.avail_out = 0) ∧ StrategyControls d result ∧ (ret=block_done → PublishReady result) ∧ after.static=h.static := by
  by_cases empty : d.sym_next = 0
  · obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
    have count := ledger.count
    rw [empty] at count
    have noSymbols : xs = [] := List.length_eq_zero_iff.mp (by simp only [UInt32.toNat_zero] at count; omega)
    subst xs
    refine ⟨0, block_done, h, z, d, ?_, ?_, buffers, stream_accounting_zero z, clear,
      rfl, rfl, rfl, available, rfl, by omega, fun _ => ⟨pending, cursor, by omega⟩,
      Or.inr rfl, ?_,⟨fun _=>cursor,rfl,rfl⟩,fun _=>⟨pending,cursor,by omega⟩,rfl⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    · simpa only [represented, Nat.add_zero] using boundary
    · intro impossible
      cases (show block_done ≠ need_more from by decide) impossible
  · obtain ⟨produced, after, z', result, run, stateA, buffersA, accountA, clearA, fields, lowA, readyA, controlsA⟩ :=
      default_foreign_flush_nonfinal_loop_boundary boundary frontier buffers positive pointer cursor memory pending bits clear available
    have static := (default_foreign_flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available false run).2.1.1.symm
    refine ⟨produced, if z'.avail_out == 0 then need_more else block_done, after, z', result,
      ?_, stateA, buffersA, accountA, clearA, ?_, ?_, ?_, ?_, ?_, lowA, readyA, ?_, ?_, controlsA, ?_,static⟩
    · unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, run]
      by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted, pure_app]
    · rw [fields]; rfl
    · rw [fields]
    · rw [fields]
    · rw [fields]; exact available
    · rw [fields]
    · by_cases exhausted : (z'.avail_out == 0) = true <;> simp [exhausted]
    · by_cases exhausted : (z'.avail_out == 0) = true
      · exact fun _ => beq_iff_eq.mp exhausted
      · simp [exhausted, show block_done ≠ need_more from by decide]

    · intro done
      by_cases exhausted : (z'.avail_out==0)=true
      · simp only [exhausted,ite_true] at done
        cases done
      · apply readyA
        have nonzero : z'.avail_out.toNat≠0 := by
          intro zero
          have wordZero : z'.avail_out=0 := UInt32.toNat_inj.mp zero
          simp only [wordZero,BEq.rfl] at exhausted
          contradiction
        omega

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual nonfinal EOF settlement, insertion reset and optional block
publication preserve the content boundary. All output capacities are
included. The subsequent public marker remains separate. -/
theorem foreign_slow_eof_nonfinal_static_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH) :
    ∃ (produced : Nat) (ret : block_state) (after : Heap) (z' : ZStream) (result : DeflateState) (ys : List Symbol),
      slowEofTail (some (.tab ds)) flush h = .ok (ret, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧ result.lookahead = 0 ∧
      result.strstart = d.strstart ∧ result.match_available = 0 ∧
      result.insert.toNat = min d.strstart.toNat 2 ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) ∧
      (ret = need_more ∨ ret = block_done) ∧ (ret = need_more → z'.avail_out = 0) ∧ StrategyControls d result ∧ (ret=block_done → PublishReady result) ∧ after.static=h.static := by
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
  obtain ⟨produced, ret, after, z', result, tailRun, boundaryA, buffersA, accountA, clearA, tailConfig,
      lookA, startA, availableA, insertA, lowA, phaseA, returns, exhausted, tailControls, doneReady,staticT⟩ :=
    foreign_finish_tail_nonfinal_static_execution insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level]; exact positive) pointer
      (by change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor)
      (by rw [configI.memory]; exact memory)
      (by change settled.pending = 0; rw [settledFrame]; exact pending) bitsI clearI settledFlag
      flush nonfinal
  have staticS := (slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun).2.1.1.symm
  refine ⟨produced, ret, after, z', result, ys, ?_, boundaryA, buffersA, accountA, clearA,
    configI.trans tailConfig, ?_, ?_, ?_, ?_, lowA, phaseA, symbols, returns, exhausted,
    ⟨tailControls.empty_cursor,tailControls.status.trans (by change settled.status=d.status;rw [settledFrame]),
      tailControls.last_flush.trans (by change settled.last_flush=d.last_flush;rw [settledFrame])⟩,doneReady,staticT.trans staticS⟩
  · unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  · rw [lookA]; exact settledLook
  · rw [startA]; exact settledStart
  · exact availableA
  · rw [insertA]
    change (eofInsert settled).insert.toNat = min d.strstart.toNat 2
    rw [eof_insert_count, settledStart]

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual nonzero non-FINISH strategy call returns with the
initialized content and EOF frontiers intact, including empty, zero and
short output. Public PARTIAL/SYNC/FULL/BLOCK markers are not part of this
internal strategy theorem. Their composition remains open. -/
theorem foreign_deflate_slow_positive_nonfinal_static_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) flush h = .ok (ret, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = block_done ∧ z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.sym_next = 0)) ∧
      StrategyControls d result ∧ (ret=block_done → PublishReady result ∧ result.match_available=0) ∧ after.static=h.static := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, stopped, stopOutput, stopInput, outputL⟩ :=
    default_foreign_slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  have staticL := (default_foreign_slow_loop_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid loop).2.1.1.symm
  have controlsL:=default_foreign_slow_loop_run_controls boundary frontier buffers positive pointer memory wrap publish inputValid
    loop stateL.good.live.hs
  rcases stopped with returned | ⟨running, broke⟩
  · refine ⟨used, produced, need_more, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      ?_, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, Or.inl ⟨rfl, stopOutput returned⟩,controlsL,(fun impossible=>by cases impossible),staticL⟩
    rw [deflate_slow_eof_tail_source, bind_app, loop]
    simp only [returned]
    rfl
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : loopD.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    obtain ⟨tailProduced, tailRet, after, z', result, tailSymbols, tailRun, contentA, buffersA, accountA,
        clearA, configA, lookA, startA, _availableA, insertA, bitsA, phaseA, _symbols, tailReturns, tailExhausted, tailControls, doneReady,staticT⟩ :=
      foreign_slow_eof_nonfinal_static_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 flush nonfinal
    have configuration : engineConfig result = config := Eq.trans configA stateL.configuration
    have strictA : result.sym_next.toNat < result.sym_end.toNat := by
      obtain ⟨_, _, trees, ledger, _⟩ := contentA.symbols
      have count := ledger.count
      have extent := trees.base.sym_end
      have lower := trees.base.lit_lo
      simp only [List.length_nil, Nat.mul_zero] at count
      omega
    have stateA : StrategyBoundary after r ds z' result extended nextOrigin (loopBase + represented tailSymbols) [] config :=
      ⟨contentA, configuration, clearA, bitsA, strictA, phaseA⟩
    have endA : EndFrontier after result := by
      have topEq : min result.strstart.toNat (fillEnd result - 2) = result.strstart.toNat - result.insert.toNat := by
        dsimp only [fillEnd]
        rw [lookA, insertA, startA]
        change min loopD.strstart.toNat (loopD.strstart.toNat + 0 - 2) = loopD.strstart.toNat - min loopD.strstart.toNat 2
        omega
      unfold EndFrontier
      rw [topEq]
      exact contentA.frontier
    have inputA : z'.avail_in = 0 := by
      have count := accountA.2.2.1
      rw [eof.2] at count
      apply UInt32.toNat_inj.mp
      change z'.avail_in.toNat = 0
      change z'.avail_in.toNat + 0 = 0 at count
      omega
    refine ⟨used, produced + tailProduced, tailRet,
      after, z', result, loopBase + represented tailSymbols, [], extended, nextOrigin,
      ?_, stateA, endA, buffersA, ?_, agreesL, ?_, Nat.le_trans baseL (Nat.le_add_right _ _), ?_,
      ⟨tailControls.empty_cursor,tailControls.status.trans controlsL.status,tailControls.last_flush.trans controlsL.last_flush⟩,
      (fun done=>⟨doneReady done,_availableA⟩),staticT.trans staticL⟩
    · rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    · simpa only [Nat.add_zero] using stream_accounting_trans accountL accountA
    · have endEq : fillEnd result = fillEnd loopD := by
        dsimp only [fillEnd]
        rw [startA, lookA, eof.1]
      rw [endEq]
      exact endpointL
    · rcases tailReturns with more | done
      · exact Or.inl ⟨more, tailExhausted more⟩
      · right
        obtain ⟨pb, buf, trees, ledger, balance⟩ := contentA.symbols
        have count := ledger.count
        have zero : result.sym_next = 0 := UInt32.toNat_inj.mp (by simpa using count)
        exact ⟨done, inputA, lookA, zero⟩

end Zlib.Deflate.Engine.Proofs

