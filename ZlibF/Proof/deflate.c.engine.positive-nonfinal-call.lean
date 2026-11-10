import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»
import ZlibF.Proof.«deflate.c.engine.nonfinal-eof-tail»

/-! # Complete actual default strategy for flushing without finishing -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual nonzero non-FINISH strategy call returns with the
initialized content and EOF frontiers intact, including empty, zero and
short output. Public PARTIAL/SYNC/FULL/BLOCK markers are not part of this
internal strategy theorem. Their composition remains open. -/
theorem deflate_slow_positive_nonfinal_ready {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
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
       (ret = block_done ∧ z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.sym_next = 0)) := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, stopped, stopOutput, stopInput, outputL⟩ :=
    slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  rcases stopped with returned | ⟨running, broke⟩
  · refine ⟨used, produced, need_more, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      ?_, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, Or.inl ⟨rfl, stopOutput returned⟩⟩
    rw [deflate_slow_eof_tail_source, bind_app, loop]
    simp only [returned]
    rfl
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : loopD.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    obtain ⟨tailProduced, tailRet, after, z', result, tailSymbols, tailRun, contentA, buffersA, accountA,
        clearA, configA, lookA, startA, _availableA, insertA, bitsA, phaseA, _symbols, tailReturns, tailExhausted⟩ :=
      slow_eof_nonfinal_tail localState endL buffersL eof.1 (by rw [levelL]; exact positive)
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
      ?_, stateA, endA, buffersA, ?_, agreesL, ?_, Nat.le_trans baseL (Nat.le_add_right _ _), ?_⟩
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
