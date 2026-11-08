import ZlibF.Proof.«deflate.c.engine.eof-zero»

/-! # Final bit-buffer facts for the complete actual FINISH call -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A finishing return of the actual complete strategy has no lookahead
or unwritten bit-buffer contents. Early output exhaustion remains distinct.
The actual loop and actual EOF tail establish these facts on the return
heap of the supplied execution. -/
theorem deflate_slow_finish_run_zero {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : after.dstates ds = some result) (finishing : ret ≠ need_more) :
    result.lookahead = 0 ∧ result.bi_valid.toInt = 0 := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    slow_finish_loop boundary frontier buffers positive pointer memory wrap output inputValid
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have same := (Prod.mk.inj (Except.ok.inj (run.symm.trans earlyRun))).1
    exact False.elim (finishing same)
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
    obtain ⟨tailRet, tailHeap, tailZ, tailD, tailRun, tailGood, look, zero⟩ :=
      slow_eof_finish_zero_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 (wrapL.trans wrap)
    have wholeRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (tailRet, tailHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have heaps : tailHeap = after := (Prod.mk.inj (Except.ok.inj (wholeRun.symm.trans run))).2
    rw [heaps] at tailGood
    have states : tailD = result := Option.some.inj (tailGood.live.hs.symm.trans live)
    rw [← states]
    exact ⟨look, zero⟩

end Zlib.Deflate.Engine.Proofs
