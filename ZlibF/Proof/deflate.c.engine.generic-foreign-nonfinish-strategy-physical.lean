import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-tail-physical»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual complete positive nonfinal strategy has exact wrapping counters,
full allocation/object effects, and its true caller byte frame at every capacity. -/
theorem default_foreign_deflate_slow_positive_nonfinal_run_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (valid : z.avail_in≠0 → z.next_in≠.null) (flush : Int32)
    (nonzero : flush≠Z_NO_FLUSH) (nonfinal : flush≠Z_FINISH)
    (run : deflate_slow (some (.tab ds)) flush h=.ok (ret,after))
    (live : r.get after=some z') (account : StreamAccounting z z' used produced) :
    z'.total_in=z.total_in+UInt64.ofNat used ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
    Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
    LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
    BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨read,written,final,loopHeap,loopZ,loopD,loopBase,loopSymbols,extended,nextOrigin,
      loop,stateL,endL,buffersL,accountL,_agrees,_endpoint,_base,stopped,_stopOutput,stopInput,outputL⟩ :=
    default_foreign_slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish valid flush nonzero
  obtain ⟨inputL,outputCountL⟩ := default_foreign_slow_loop_run_counter_effects boundary frontier buffers positive pointer memory wrap publish valid
    loop stateL.good.live.hz accountL
  obtain ⟨shapeL,frameL,_liveL,allocL,nextL⟩ := default_foreign_slow_loop_run_full_storage boundary frontier buffers positive pointer memory wrap publish valid loop
  have preciseL := default_foreign_slow_loop_run_buffer_frame boundary frontier buffers positive pointer memory wrap publish valid
    loop stateL.good.live.hz accountL
  rcases stopped with returned|⟨running,broke⟩
  · have actual : deflate_slow (some (.tab ds)) flush h=.ok (need_more,loopHeap) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [returned]
      rfl
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst after
    have streams : loopZ=z' := Option.some.inj (stateL.good.live.hz.symm.trans live)
    subst z'
    have counts := stream_accounting_counts_unique accountL account
    rw [counts.1] at inputL
    rw [counts.2] at outputCountL preciseL
    exact ⟨inputL,outputCountL,shapeL,frameL,full_shape_live_change shapeL,allocL,nextL,preciseL⟩
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out=.ref (.dstate_depth owner) (oo+written) := by
      rw [accountL.2.2.2.2.2.1,pointer]
      rfl
    have levelL : loopD.level=config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize=config.memory := congrArg EngineConfig.memory stateL.configuration
    obtain ⟨amount,tailRet,other,otherZ,otherD,_ys,tailRun,contentA,_buffersA,accountT,_rest⟩ :=
      default_foreign_slow_eof_nonfinal_tail localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 flush nonfinal
    obtain ⟨inputT,outputT,shapeT,frameT,_liveT,allocT,nextT⟩ :=
      foreign_nonfinal_eof_run_physical localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 flush nonfinal tailRun contentA.good.live.hz accountT
    have preciseT := foreign_nonfinal_eof_run_buffer_frame localState endL buffersL eof.1 (by rw [levelL];exact positive)
      pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 flush nonfinal tailRun contentA.good.live.hz accountT
    have owned := ConfigFrame.owned (ds:=ds) (show ConfigFrame d loopD from stateL.configuration.trans boundary.configuration.symm)
    rw [owned] at frameT preciseT
    have shape := shapeL.trans shapeT
    have frame := full_frame_trans_shape frameL frameT shapeL
    rw [pointerL] at preciseT
    rw [pointer] at preciseL
    obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
    have precise := foreign_buffer_frame_adjacent preciseL preciseT shapeL shapeT boundary.good.uniq get
      (caller_foreign_owner_outside boundary.good buffers pointer)
    have actual : deflate_slow (some (.tab ds)) flush h=.ok (tailRet,other) := by
      rw [deflate_slow_eof_tail_source,bind_app,loop]
      simp only [running]
      exact tailRun
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst after
    have streams : otherZ=z' := Option.some.inj (contentA.good.live.hz.symm.trans live)
    subst z'
    have counts := stream_accounting_counts_unique (stream_accounting_trans accountL accountT) account
    have totals := stream_counter_effects_trans inputL outputCountL (show otherZ.total_in=loopZ.total_in+UInt64.ofNat 0 by simpa using inputT) outputT
    simp only [Nat.add_zero] at counts totals
    rw [counts.1] at totals
    rw [counts.2] at totals precise
    exact ⟨totals.1,totals.2,shape,frame,full_shape_live_change shape,allocT.trans allocL,nextT.trans nextL,by simpa only [pointer] using precise⟩
end Zlib.Deflate.Engine.Proofs
