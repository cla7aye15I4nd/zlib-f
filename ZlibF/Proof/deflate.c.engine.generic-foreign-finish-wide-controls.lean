import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-controls»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual prepared FINISH strategy preserves status, last_flush and empty cursor
at every caller capacity. Actual all-capacity loop and EOF controls are composed;
no positive-output whole-strategy control theorem is used. -/
theorem default_foreign_deflate_slow_finish_ready_run_controls {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out= .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h= .ok (ret,after)) (live : after.dstates ds=some result) :
    StrategyControls d result := by
  obtain ⟨used,produced,final,loopHeap,loopZ,loopD,loopBase,loopSymbols,extended,nextOrigin,
    loop,stateL,endL,buffersL,accountL,_agreesL,_endpointL,_baseL,stopped,_stopOutput,stopInput,outputL⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  have controlsL := default_foreign_slow_loop_run_controls boundary frontier buffers positive pointer memory wrap publish inputValid loop stateL.good.live.hs
  rcases stopped with returned|⟨running,broke⟩
  · have tested : deflate_slow (some (.tab ds)) Z_FINISH h= .ok (need_more,loopHeap) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [returned,pure_app]
    have heaps : loopHeap=after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [heaps] at stateL
    have states : loopD=result := Option.some.inj (stateL.good.live.hs.symm.trans live)
    rw [← states]
    exact controlsL
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out= .ref (.dstate_depth owner) (oo+produced) := by
      rw [accountL.2.2.2.2.2.1,pointer]
      rfl
    have levelL : loopD.level=config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize=config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : loopD.wrap=config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced,tailHeap,tailZ,tailD,_ys,_before,_written,_remaining,_kind,_body,_padding,
      tailRun,stateT,_buffersT,_accountT,_rest⟩ :=
      default_foreign_slow_eof_finish_tail_encoding localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap)
    have controlsT := default_foreign_slow_eof_finish_run_controls localState endL buffersL eof.1 (by rw [levelL];exact positive)
      pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap) tailRun stateT.good.live.hs
    have tested : deflate_slow (some (.tab ds)) Z_FINISH h=
        .ok ((if tailZ.avail_out==0 then finish_started else finish_done),tailHeap) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [running]
      exact tailRun
    have heaps : tailHeap=after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [heaps] at stateT
    have states : tailD=result := Option.some.inj (stateT.good.live.hs.symm.trans live)
    rw [← states]
    exact ⟨controlsT.empty_cursor,controlsT.status.trans controlsL.status,controlsT.last_flush.trans controlsL.last_flush⟩


end Zlib.Deflate.Engine.Proofs
