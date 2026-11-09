import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-return-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-no-flush-physical»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete actual prepared marker dispatch, including private stores and adjacent caller publication. -/
theorem public_foreign_busy_marker_data_physical_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (memory : config.memory.toNat=16384)
    (wrap : config.wrap=1) (publish : PublishReady d) (valid : z.avail_in≠0 → z.next_in≠.null)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) flush h=.ok (Z_OK,after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in=z.total_in+UInt64.ofNat used ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have nonzero : flush≠Z_NO_FLUSH := by rcases flag with e|e|e|e <;> rw [e] <;> decide
  have nonfinal : flush≠Z_FINISH := by rcases flag with e|e|e|e <;> rw [e] <;> decide
  have positive : 0<config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level=config.level at eq
    rw [←eq,level]
    decide
  obtain ⟨used,produced,ret,middle,zm,dm,bm,ys,nextInput,nextOrigin,strategyRun,stateM,endM,buffersM,
      accountM,_agrees,_endpoint,_base,classification,controls,doneReady⟩ :=
    default_foreign_deflate_slow_positive_nonfinal_ready (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish valid flush nonzero nonfinal
  obtain ⟨inputM,outputM,shapeM,frameM,_liveM,allocM,nextM,preciseM⟩ :=
    default_foreign_deflate_slow_positive_nonfinal_run_effects (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish valid flush nonzero nonfinal strategyRun stateM.good.live.hz accountM
  have source : publicDataTail (some r) (some (.tab ds)) flush h=
      publicStrategyReturn (some r) (some (.tab ds)) flush ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy flush nonzero]
    simp only [bind_app,strategyRun]
  rcases classification with ⟨returned,exhausted⟩|⟨returned,_input,look,symbols⟩
  · subst ret
    have returned := public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted flush
    have storage := full_storage_state_trans shapeM frameM allocM nextM stateM.good.live.hs
      (Or.inr (Or.inl (Or.inl rfl))) {dm with last_flush:= -1}
    exact ⟨used,produced,_,zm,_,source.trans returned,last_flush_good stateM.good (-1),accountM,inputM,outputM,
      storage.1,storage.2.1,storage.2.2.1,storage.2.2.2.1,storage.2.2.2.2,
      foreign_finish_scalar_buffer_frame boundary.good buffers pointer stateM.good.live.hs rfl preciseM⟩
  · subst ret
    have readyM := (doneReady rfl).1
    have available := (doneReady rfl).2
    obtain ⟨pb,buf,treesM,ledger,_balance⟩ := stateM.symbols
    have ysNil : ys=[] := by
      have count := ledger.count
      rw [symbols] at count
      apply List.length_eq_zero_iff.mp
      change 0=3*ys.length at count
      omega
    subst ys
    have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+produced) := by
      rw [accountM.2.2.2.2.2.1,pointer]
      rfl
    obtain ⟨amount,after,z',result,markerRun,goodA,accountA,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
      foreign_nonfinish_marker_return_physical_execution (stateM.buffered endM controls.empty_cursor)
        buffersM treesM pointerM readyM look available flush flag
    have owned := ConfigFrame.owned (ds:=ds) (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm)
    rw [owned] at frameA preciseA
    have shape := shapeM.trans shapeA
    have frame := full_frame_trans_shape frameM frameA shapeM
    rw [pointerM] at preciseA
    rw [pointer] at preciseM
    obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
    have precise := foreign_buffer_frame_adjacent preciseM preciseA shapeM shapeA boundary.good.uniq get
      (caller_foreign_owner_outside boundary.good buffers pointer)
    have totals := stream_counter_effects_trans inputM outputM
      (show z'.total_in=zm.total_in+UInt64.ofNat 0 by simpa using inputA) outputA
    exact ⟨used,produced+amount,after,z',result,source.trans markerRun,goodA,
      by simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA,
      by simpa only [Nat.add_zero] using totals.1,totals.2,
      shape,frame,full_shape_live_change shape,allocA.trans allocM,nextA.trans nextM,by simpa only [pointer] using precise⟩
end Zlib.Deflate.Engine.Proofs
