import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-strategy-environment»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-block-data-safety»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Restoring a depth-array caller region leaves the static environment unchanged. -/
theorem foreign_marker_depth_buffer_frame_static {h after : Heap} {owner oo n : Nat}
    {changed : Nat → Prop}
    (frame : BufferFrame h after changed [⟨.ref (.dstate_depth owner) oo,n⟩]) :
    after.static=h.static := by
  have eq := frame.1.1
  cases beforeGet : h.dstates owner <;> cases afterGet : after.dstates owner <;>
    simpa [restoreRegions,Space.get,Space.put,beforeGet,afterGet] using eq.symm

/-- Every actual prepared marker data dispatch retains the static environment.
All prepared output capacities, including zero, are admitted. -/
theorem public_foreign_busy_marker_data_run_static {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (memory : config.memory.toNat=16384)
    (wrap : config.wrap=1) (publish : PublishReady d) (valid : z.avail_in≠0 → z.next_in≠.null)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK)
    (run : publicDataTail (some r) (some (.tab ds)) flush h=.ok (rc,after)) :
    after.static=h.static := by
  have nonzero : flush≠Z_NO_FLUSH := by rcases flag with e|e|e|e <;> rw [e] <;> decide
  have nonfinal : flush≠Z_FINISH := by rcases flag with e|e|e|e <;> rw [e] <;> decide
  have positive : 0<config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level=config.level at eq
    rw [←eq,level]
    decide
  obtain ⟨used,produced,ret,middle,zm,dm,bm,ys,nextInput,nextOrigin,strategyRun,stateM,endM,buffersM,
      accountM,_agrees,_endpoint,_base,classification,controls,doneReady,staticM⟩ :=
    foreign_deflate_slow_positive_nonfinal_static_execution (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish valid flush nonzero nonfinal
  have source : publicDataTail (some r) (some (.tab ds)) flush h=
      publicStrategyReturn (some r) (some (.tab ds)) flush ret middle := by
    rw [public_busy_positive_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy flush nonzero]
    simp only [bind_app,strategyRun]
  have actualReturn := source.symm.trans run
  rcases classification with ⟨returned,exhausted⟩|⟨returned,_input,look,symbols⟩
  · subst ret
    have actual := public_strategy_need_more_request stateM.good.live.hz stateM.good.live.hs exhausted flush
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
    rw [←heaps]
    exact staticM
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
    have boundaryM := stateM.buffered endM controls.empty_cursor
    rcases flag with partialFlag|syncFlag|fullFlag|blockFlag
    · subst flush
      obtain ⟨amount,other,z',result,written,actual,_state,_buffers,_account,_bytes,_config,_status,_last,
          _adler,_end,_available,_interval,_in,_out,_sizes,storage,_precise,_ready⟩ :=
        public_strategy_foreign_partial_done boundaryM buffersM treesM pointerM readyM
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
      exact heaps ▸ storage.frame.1.symm.trans staticM
    · subst flush
      obtain ⟨amount,other,z',result,written,remaining,actual,_state,_buffers,_account,_bytes,_pending,_wire,
          _config,_status,_last,_adler,_end,_available,_interval,_in,_out,_sizes,storage,_precise,_ready⟩ :=
        public_strategy_foreign_sync_done boundaryM buffersM treesM pointerM readyM
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
      exact heaps ▸ storage.frame.1.symm.trans staticM
    · subst flush
      obtain ⟨amount,other,z',result,written,remaining,actual,_state,_buffers,_account,_bytes,_pending,_wire,
          _config,_status,_last,_adler,_end,_available,_endpoint,_interval,_in,_out,_sizes,_shape,_alloc,_next,precise,_ready⟩ :=
        public_strategy_foreign_full_done boundaryM buffersM treesM pointerM readyM look available
      rw [pointerM] at precise
      have static := foreign_marker_depth_buffer_frame_static precise
      have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
      exact heaps ▸ static.trans staticM
    · subst flush
      have actual := public_strategy_block_done_ready stateM.good readyM
      by_cases exhausted : (zm.avail_out==0)=true
      · simp only [exhausted,ite_true] at actual
        have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
        rw [←heaps]
        exact staticM
      · simp only [exhausted,Bool.false_eq_true,ite_false] at actual
        have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans actualReturn))).2
        exact heaps ▸ staticM
end Zlib.Deflate.Engine.Proofs
