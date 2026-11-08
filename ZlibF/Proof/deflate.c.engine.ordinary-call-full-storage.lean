import ZlibF.Proof.«deflate.c.engine.no-flush-full-storage»
import ZlibF.Proof.«deflate.c.engine.finish-tail-full-storage»
import ZlibF.Proof.«deflate.c.engine.finish-call-counters»

/-! # Complete ordinary strategy heap frames -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual complete FINISH strategy return, including early output exhaustion and the complete final tail, retains the full object/allocation frame. -/
theorem deflate_slow_finish_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  obtain ⟨shapeL, frameL, _liveL, allocL, nextL⟩ := slow_ordinary_loop_run_full_storage (Or.inr rfl)
    boundary frontier buffers positive pointer memory wrap publish inputValid loop
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have eq := (Prod.mk.inj (Except.ok.inj (earlyRun.symm.trans run))).2
    rw [← eq]
    exact ⟨shapeL, frameL, full_shape_live_change shapeL, allocL, nextL⟩
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
    have wrapL : loopD.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced, tailRet, tailHeap, tailZ, tailD, tailRun, tailGood, accountT, inputT, outputT, shapeT, frameT, _liveT, allocT, nextT⟩ :=
      slow_eof_finish_full_storage_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 (wrapL.trans wrap)
    have wholeRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (tailRet, tailHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have eq := (Prod.mk.inj (Except.ok.inj (wholeRun.symm.trans run))).2
    rw [← eq]
    have owned := ConfigFrame.owned (ds := ds) (show ConfigFrame d loopD from stateL.configuration.trans boundary.configuration.symm)
    rw [owned] at frameT
    have shape := shapeL.trans shapeT
    have frame := full_frame_trans_shape frameL frameT shapeL
    exact ⟨shape, frame, full_shape_live_change shape, allocT.trans allocL, nextT.trans nextL⟩

/-- Both complete actual ordinary strategy calls retain the full private/output frame and exact object/allocation ledgers. -/
theorem deflate_slow_ordinary_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with rfl | rfl
  · exact deflate_slow_no_flush_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid run
  · exact deflate_slow_finish_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid run

end Zlib.Deflate.Engine.Proofs
