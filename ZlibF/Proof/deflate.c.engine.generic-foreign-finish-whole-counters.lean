import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-final-effects»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.finish-call-counters»

/-! # The complete actual FINISH strategy has exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual complete FINISH strategy return retains exact wrapping counters. -/
theorem default_foreign_deflate_slow_finish_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds owner oo origin base accepted delivered : Nat}
    {z returnedZ : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : r.get after = some returnedZ) (account : StreamAccounting z returnedZ accepted delivered) :
    returnedZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      returnedZ.total_out = z.total_out + UInt64.ofNat delivered := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  have effectsL := default_foreign_slow_loop_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid
    loop stateL.good.live.hz accountL
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have same := actual_run_stream_unique earlyRun run stateL.good.live.hz live
    exact stream_counter_effects_identify same accountL account effectsL.1 effectsL.2
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
    obtain ⟨tailProduced, tailRet, tailHeap, tailZ, tailD, tailRun, tailGood, accountT, inputT, outputT, _adlerT⟩ :=
      default_foreign_slow_eof_finish_effect_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 (wrapL.trans wrap)
    have wholeRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (tailRet, tailHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have same := actual_run_stream_unique wholeRun run tailGood.live.hz live
    have combined := stream_accounting_trans accountL accountT
    have effects := stream_counter_effects_trans (used := used) (first := 0) (produced := produced) (second := tailProduced)
      effectsL.1 effectsL.2 (by simpa using inputT) outputT
    exact stream_counter_effects_identify same combined account effects.1 effects.2

end Zlib.Deflate.Engine.Proofs
