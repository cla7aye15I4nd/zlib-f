import ZlibF.Proof.«deflate.c.engine.nonfinal-eof-effects»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

/-! # Exact effects through the complete actual nonfinal strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual terminating loop and real nonfinal EOF tail have the same
exact counters, output interval and complete object/allocation frame on
the returned heap. The execution premise can be supplied by the proved
complete strategy theorem; no callee contract is assumed. -/
theorem deflate_slow_nonfinal_run_effects {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base accepted delivered : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' accepted delivered) :
    z'.total_in = z.total_in + UInt64.ofNat accepted ∧ z'.total_out = z.total_out + UInt64.ofNat delivered ∧
      RawOutputInterval h after ob oo delivered ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped,
      _stopOutput, stopInput, outputL, inputL, totalsL, intervalL, shapeL, frameL, liveL, allocL, nextL, _controlsL⟩ :=
    slow_positive_loop_safety boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) flush h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have heaps : loopHeap = after := (Prod.mk.inj (Except.ok.inj (earlyRun.symm.trans run))).2
    have streams : loopZ = z' := by
      rw [heaps] at stateL
      exact Option.some.inj (stateL.good.live.hz.symm.trans live)
    have totals := stream_counter_effects_identify streams accountL account inputL totalsL
    have interval := RawOutputInterval.identify earlyRun run stateL.good.live.hz
      live accountL account intervalL
    refine ⟨totals.1, totals.2, interval, ?_⟩
    rw [← heaps]
    exact ⟨shapeL, frameL, liveL, allocL, nextL⟩
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
    obtain ⟨tailProduced, tailRet, tailHeap, tailZ, tailD, tailRun, goodT, accountT,
        inputT, totalsT, intervalT, shapeT, frameT, _liveT, allocT, nextT⟩ :=
      slow_eof_nonfinal_effect_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 flush nonfinal
    have wholeRun : deflate_slow (some (.tab ds)) flush h = .ok (tailRet, tailHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have wholeAccount : StreamAccounting z tailZ used (produced + tailProduced) := by
      simpa only [Nat.add_zero] using stream_accounting_trans accountL accountT
    have inputT' : tailZ.total_in = loopZ.total_in + UInt64.ofNat 0 := by simpa using inputT
    have totals := stream_counter_effects_trans inputL totalsL inputT' totalsT
    have interval := intervalL.trans intervalT
    have configL : ConfigFrame d loopD := stateL.configuration.trans boundary.configuration.symm
    rw [configL.owned (ds := ds)] at frameT
    have shape := shapeL.trans shapeT
    have storage : Shape h tailHeap ∧ Frame h tailHeap (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
        LiveChange h tailHeap (fun _ => False) (fun _ => False) ∧ tailHeap.nalloc = h.nalloc ∧ tailHeap.nextBlk = h.nextBlk :=
      ⟨shape, full_frame_trans_shape frameL frameT shapeL, full_shape_live_change shape,
        allocT.trans allocL, nextT.trans nextL⟩
    have heaps : tailHeap = after := (Prod.mk.inj (Except.ok.inj (wholeRun.symm.trans run))).2
    have streams : tailZ = z' := by
      rw [heaps] at goodT
      exact Option.some.inj (goodT.live.hz.symm.trans live)
    have finalTotals := stream_counter_effects_identify streams wholeAccount account totals.1 totals.2
    have finalInterval := RawOutputInterval.identify wholeRun run goodT.live.hz
      live wholeAccount account interval
    refine ⟨finalTotals.1, finalTotals.2, finalInterval, ?_⟩
    rw [← heaps]
    exact storage

end Zlib.Deflate.Engine.Proofs
