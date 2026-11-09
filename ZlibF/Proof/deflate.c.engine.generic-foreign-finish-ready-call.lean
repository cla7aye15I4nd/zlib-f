import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual prepared FINISH includes its terminating loop and real EOF tail at every
caller output capacity. The original final-return classification is retained. -/
theorem default_foreign_deflate_slow_finish_ready {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (ret ≠ need_more → result.lookahead = 0 ∧ result.bi_valid.toInt = 0) ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, stopped, stopOutput, stopInput, outputL⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  rcases stopped with returned | ⟨running, broke⟩
  · refine ⟨used, produced, need_more, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      ?_, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, (fun impossible => False.elim (impossible rfl)), Or.inl ⟨rfl, stopOutput returned⟩⟩
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
    have wrapL : loopD.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced,after,z',result,tailSymbols,_before,_written,_remaining,_kind,_body,_padding,
        tailRun,contentA,buffersA,accountA,clearA,configA,lookA,startA,_availableA,insertA,bitsA,phaseA,_symbols,
        finalA,_rest⟩ :=
      default_foreign_slow_eof_finish_tail_encoding localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap)
    have zeroA : result.lookahead=0 ∧ result.bi_valid.toInt=0 := by
      have lower := contentA.good.inv.bits.1
      exact ⟨lookA,by omega⟩
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
    refine ⟨used, produced + tailProduced, if z'.avail_out == 0 then finish_started else finish_done,
      after, z', result, loopBase + represented tailSymbols, [], extended, nextOrigin,
      ?_, stateA, endA, buffersA, ?_, agreesL, ?_, Nat.le_trans baseL (Nat.le_add_right _ _), (fun _ => zeroA), ?_⟩
    · rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    · simpa only [Nat.add_zero] using stream_accounting_trans accountL accountA
    · have endEq : fillEnd result = fillEnd loopD := by
        dsimp only [fillEnd]
        rw [startA, lookA, eof.1]
      rw [endEq]
      exact endpointL
    · by_cases empty : z'.avail_out = 0
      · right; left
        exact ⟨by simp [empty], empty, inputA⟩
      · right; right
        have nonzero : z'.avail_out.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        exact ⟨by simp [empty], by omega, inputA⟩

end Zlib.Deflate.Engine.Proofs
