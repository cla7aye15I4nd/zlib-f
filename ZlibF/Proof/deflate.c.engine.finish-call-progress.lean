import ZlibF.Proof.«deflate.c.engine.finish-loop-progress»
import ZlibF.Proof.«deflate.c.engine.strategy-finish»
import ZlibF.Proof.«deflate.c.engine.finish-buffered»

/-! # Complete actual FINISH calls progress before output retry -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real strategy either enters final publication or strictly reduces
unread input plus lookahead. Output capacity may be any positive amount;
this result needs no total compressed-size estimate. -/
theorem deflate_slow_finish_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) ∧
      (ret = need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, stopped, stopOutput, stopInput, outputL, strictL⟩ :=
    slow_finish_loop_progress boundary frontier buffers positive pointer memory wrap output inputValid
  rcases stopped with returned | ⟨running, broke⟩
  · refine ⟨used, produced, need_more, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      ?_, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, Or.inl ⟨rfl, stopOutput returned⟩, fun _ => strictL returned⟩
    rw [deflate_slow_eof_tail_source, bind_app, loop]
    simp only [returned]
    rfl
  · have eof := stopInput broke
    have readyL := stateL.resume (outputL running)
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : loopD.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : loopD.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced, after, z', result, tailSymbols, tailRun, contentA, buffersA, accountA,
        clearA, configA, lookA, startA, _availableA, insertA, bitsA, phaseA, _symbols⟩ :=
      slow_eof_finish_tail localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 (wrapL.trans wrap)
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
      ?_, stateA, endA, buffersA, ?_, agreesL, ?_, Nat.le_trans baseL (Nat.le_add_right _ _), ?_, ?_⟩
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

    · intro impossible
      split at impossible
      · cases (by decide : finish_started ≠ need_more) impossible
      · cases (by decide : finish_done ≠ need_more) impossible

/-- The caller-independent buffered boundary has the same strict
need_more progress. Both properties refer to the identical real run. -/
theorem deflate_slow_finish_buffered_progress {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (output : 0 < z.avail_out.toNat) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StrategyControls d result ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (ret ≠ need_more → result.lookahead = 0 ∧ result.bi_valid.toInt = 0) ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) ∧
      (ret = need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  obtain ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin,
      run, stateA, controls, resume, buffersA, account, agrees, endpoint, baseLe, zero, classification⟩ :=
    deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  obtain ⟨_usedP, _producedP, retP, afterP, zP, resultP, _baseP, _ysP, _extendedP, _originP,
      runP, stateP, _endP, _buffersP, _accountP, _agreesP, _endpointP, _baseLeP, _classificationP, strict⟩ :=
    deflate_slow_finish_progress (boundary.strategy publish) boundary.end_frontier buffers
      positive pointer memory wrap output inputValid
  obtain ⟨code, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
  subst retP afterP
  have streams : zP = z' := Option.some.inj (stateP.good.live.hz.symm.trans stateA.good.live.hz)
  have states : resultP = result := Option.some.inj (stateP.good.live.hs.symm.trans stateA.good.live.hs)
  subst zP resultP
  exact ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin,
    run, stateA, controls, resume, buffersA, account, agrees, endpoint, baseLe, zero, classification, strict⟩

end Zlib.Deflate.Engine.Proofs
