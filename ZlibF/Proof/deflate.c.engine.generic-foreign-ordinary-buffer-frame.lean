import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual prepared NO_FLUSH strategy has its full byte frame, including zero capacity. -/
theorem default_foreign_deflate_slow_no_flush_run_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo origin base used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' used produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  rw [deflate_slow_eof_tail_source] at run
  cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
  | error fault => simp only [bind_app,loop] at run;cases run
  | ok pair =>
    obtain ⟨final,middle⟩ := pair
    have returned := default_foreign_slow_no_flush_ready_loop_run_control boundary frontier buffers positive pointer memory wrap publish inputValid loop
    simp only [bind_app,loop,returned,pure_app] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact default_foreign_slow_loop_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish inputValid loop live account

/-- The complete actual prepared FINISH strategy composes the loop and final-tail byte frames.
Early output exhaustion and zero caller capacity are both admitted. -/
theorem default_foreign_deflate_slow_finish_run_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo origin base used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' used produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨read, written, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  have frameL := default_foreign_slow_loop_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish inputValid
    loop stateL.good.live.hz accountL
  obtain ⟨shapeL,_restL⟩ := default_foreign_slow_loop_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid loop
  rcases stopped with returned | ⟨running,broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more,loopHeap) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [returned]
      rfl
    have heaps := (Prod.mk.inj (Except.ok.inj (earlyRun.symm.trans run))).2
    subst after
    have streams : loopZ=z' := Option.some.inj (stateL.good.live.hz.symm.trans live)
    rw [streams] at accountL
    have counts := stream_accounting_counts_unique accountL account
    rw [counts.2] at frameL
    exact frameL
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.dstate_depth owner) (oo+written) := by
      rw [accountL.2.2.2.2.2.1,pointer]
      rfl
    have levelL : loopD.level=config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize=config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : loopD.wrap=config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced,tailHeap,tailZ,tailD,_ys,_before,_written,_remaining,_kind,_body,_padding,
      tailRun,tailBoundary,_buffersT,accountT,_clearT,_configT,_lookT,_startT,_matchT,_insertT,
      _lowT,_readyT,_symbolsT,_zeroT,_pendingT,_bytesT,_pendingA,_kindT,_padT,_storedT,_wireT,_grammarT,frameT⟩ :=
      default_foreign_slow_eof_finish_tail_encoding localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap)
    have wholeRun : deflate_slow (some (.tab ds)) Z_FINISH h =
        .ok ((if tailZ.avail_out == 0 then finish_started else finish_done),tailHeap) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [running]
      exact tailRun
    have heaps := (Prod.mk.inj (Except.ok.inj (wholeRun.symm.trans run))).2
    subst after
    obtain ⟨shapeT,_restT⟩ := default_foreign_slow_eof_finish_run_full_storage localState endL buffersL eof.1
      (by rw [levelL];exact positive) pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap) tailRun
    have owned := ConfigFrame.owned (ds:=ds) (show ConfigFrame d loopD from stateL.configuration.trans boundary.configuration.symm)
    rw [owned,pointerL] at frameT
    rw [pointer] at frameL
    obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
    have composed := foreign_buffer_frame_adjacent frameL frameT shapeL shapeT boundary.good.uniq get
      (caller_foreign_owner_outside boundary.good buffers pointer)
    have streams : tailZ=z' := Option.some.inj (tailBoundary.good.live.hz.symm.trans live)
    rw [streams] at accountT
    have counts := stream_accounting_counts_unique (stream_accounting_trans accountL accountT) account
    rw [counts.2] at composed
    simpa only [pointer] using composed

/-- Both complete actual ordinary strategy calls have their full caller byte frame. -/
theorem default_foreign_deflate_slow_ordinary_run_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo origin base used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state} {flush : Int32}
    (flag : flush=Z_NO_FLUSH ∨ flush=Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret,after))
    (live : r.get after = some z') (account : StreamAccounting z z' used produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  rcases flag with rfl | rfl
  · exact default_foreign_deflate_slow_no_flush_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  · exact default_foreign_deflate_slow_finish_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish inputValid run live account

end Zlib.Deflate.Engine.Proofs
