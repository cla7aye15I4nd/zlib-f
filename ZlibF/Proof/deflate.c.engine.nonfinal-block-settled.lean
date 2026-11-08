import ZlibF.Proof.«deflate.c.engine.nonfinal-call-controls»

/-! # An actual completed flushing strategy has settled deferred input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual block_done from a flushing slow call has settled its deferred
literal. An early loop return is need_more and cannot reach this cutpoint. -/
theorem deflate_slow_nonfinal_run_block_settled {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (block_done, after))
    (live : after.dstates ds = some result) : result.match_available = 0 := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) flush h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have bad : need_more = block_done := (Prod.mk.inj (Except.ok.inj (earlyRun.symm.trans run))).1
    cases (show need_more ≠ block_done from by decide) bad
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
    have tailRun : slowEofTail (some (.tab ds)) flush loopHeap = .ok (block_done, after) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop] at run
      simpa only [running] using run
    obtain ⟨_tailProduced, _tailRet, computed, _z', computedD, _tailSymbols, computedRun,
        contentA, _buffersA, _accountA, _clearA, _configA, _lookA, _startA, settledA,
        _insertA, _bitsA, _phaseA, _symbols, _returns, _exhausted⟩ :=
      slow_eof_nonfinal_tail localState endL buffersL eof.1
        (by rw [levelL]; exact positive) pointerL readyL.2.1 (by rw [memoryL]; exact memory)
        readyL.1 flush nonfinal
    have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (computedRun.symm.trans tailRun))).2
    have states : computedD = result := by
      have state := contentA.good.live.hs
      rw [heaps] at state
      exact Option.some.inj (state.symm.trans live)
    rw [← states]
    exact settledA

end Zlib.Deflate.Engine.Proofs
