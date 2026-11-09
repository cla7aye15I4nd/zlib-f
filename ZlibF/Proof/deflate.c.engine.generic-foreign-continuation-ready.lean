import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-match-full»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-search»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonpublishing-encoding»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual continuation is publication-ready even when entry capacity is zero.
The explicit comparison room is supplied by the surrounding body cutpoint. -/
theorem default_foreign_slow_decision_run_ready {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {head : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (lookahead : 1≤d.lookahead.toNat) (strict : d.sym_next.toNat<d.sym_end.toNat)
    (positive : 0<d.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat=16384) (comparisonRoom : d.strstart.toNat+262≤d.window_size.toNat)
    (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st head h=.ok (next,after))
    (live : after.dstates ds=some result) : next.ret=none → PublishReady result := by
  have identify {expected : LoopS} {other : Heap} {otherD : DeflateState}
      (actual : slowDecision (some (.tab ds)) flush st head h=.ok (expected,other))
      (get : other.dstates ds=some otherD) (phase : expected.ret=none → PublishReady otherD) :
      next.ret=none → PublishReady result := by
    have pair := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
    rw [pair.2] at get
    have same := Option.some.inj (get.symm.trans live)
    simpa only [pair.1,same] using phase
  by_cases selected : (d.prev_length≥MIN_MATCH_u && d.match_length≤d.prev_length)=true
  · by_cases full : (d.sym_next+3==d.sym_end)=true
    · obtain ⟨produced,candidate,other,z',otherD,_before,_written,_remaining,_kind,_body,
        actual,stateA,_endA,_buffersA,_accountA,_clearA,_configA,_startA,_lookA,_endpoint,
        _strictA,_smallA,_bitsA,phaseA,_cursorA,_rest⟩ :=
        default_foreign_slow_match_full_encoding cut buffers selected strict full positive pointer memory ready clear comparisonRoom flush st head
      apply identify actual stateA.good.live.hs
      intro running
      have output : 0<z'.avail_out.toNat := by
        by_cases empty : z'.avail_out=0
        · simp only [empty,BEq.rfl,ite_true] at running
          cases running
        · have nz : z'.avail_out.toNat≠0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
      exact phaseA output
    · have nonfull := Bool.eq_false_iff.mpr full
      obtain ⟨candidate,other,otherD,_before,actual,stateA,_endA,_buffersA,_accountA,_clearA,
        _startA,_lookA,_endpoint,_strictA,_configA,_bitsA,phaseA,_rest⟩ :=
        default_foreign_slow_match_nonfull_search_encoding cut buffers selected strict nonfull pointer ready.2.1 ready.1 ready.2.2 clear flush st head
      exact identify actual stateA.good.live.hs (fun _=>phaseA)
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available=0
    · obtain ⟨other,otherD,_before,actual,stateA,_endA,_buffersA,_accountA,_clearA,
        _startA,_lookA,_endpoint,_strictA,_configA,_bitsA,phaseA,_rest⟩ :=
        default_foreign_slow_defer_search_encoding cut buffers lookahead branch available strict pointer ready.2.1 ready.1 ready.2.2 clear flush st head
      exact identify actual stateA.good.live.hs (fun _=>phaseA)
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat+3=d.sym_end.toNat
      · obtain ⟨produced,other,z',otherD,_before,_written,_remaining,_kind,_body,
          actual,stateA,_endA,_buffersA,_accountA,_clearA,_startA,_lookA,_endpoint,
          _strictA,_configA,_bitsA,phaseA,_cursorA,_smallA,_rest⟩ :=
          default_foreign_slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer
            ready.2.1 memory comparisonRoom ready.1 (by have low:=ready.2.2;omega) clear flush st head
        apply identify actual stateA.good.live.hs
        intro running
        have output : 0<z'.avail_out.toNat := by
          by_cases empty : z'.avail_out=0
          · simp only [empty,BEq.rfl,ite_true] at running
            cases running
          · have nz : z'.avail_out.toNat≠0 := fun zero => empty (UInt32.toNat_inj.mp zero)
            omega
        exact phaseA output
      · have space : d.sym_next.toNat+3<d.sym_end.toNat := by omega
        obtain ⟨other,otherD,_before,actual,stateA,_endA,_buffersA,_accountA,_clearA,
          _startA,_lookA,_endpoint,_strictA,_configA,_bitsA,phaseA,_rest⟩ :=
          default_foreign_slow_literal_nonfull_search_encoding cut buffers lookahead branch available space pointer ready.2.1 ready.1 ready.2.2 clear flush st head
        exact identify actual stateA.good.live.hs (fun _=>phaseA)

/-- Actual initialized search retains the zero-capacity continuation phase. -/
theorem default_foreign_slow_search_run_ready {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1≤d.lookahead.toNat)
    (comparisonRoom : d.strstart.toNat+262≤d.window_size.toNat)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h=.ok (next,after))
    (live : after.dstates ds=some result) : next.ret=none → PublishReady result := by
  obtain ⟨w,wa,head,found,searched,searchRun,cut,searchFrame,searchedBuffers,_storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers (fun _=>comparisonRoom)
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame;rw [searchFrame]
  have configS : engineConfig searched=config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level=config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize=config.memory := congrArg EngineConfig.memory configS
  have decisionRun : slowDecision (some (.tab ds)) flush st head found=.ok (next,after) := by
    unfold slowSearchDecision at run
    simpa only [bind_app,searchRun] using run
  exact default_foreign_slow_decision_run_ready cut searchedBuffers
    (by rw [searchFrame];exact lookahead) (by rw [searchFrame];exact boundary.strict)
    (by rw [levelS];exact positive) pointer (by rw [memoryS];exact memory)
    (by rw [searchFrame];exact comparisonRoom) (ready.slow slowFrame) (boundary.clear.slow slowFrame) decisionRun live

/-- Every signed-flush actual body continues publication-ready, including zero entry output. -/
theorem default_foreign_slow_body_run_ready_phase {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (run : deflate_slow_body (some (.tab ds)) flush st h=.ok (next,after))
    (live : after.dstates ds=some result) : next.ret=none → PublishReady result := by
  by_cases short : d.lookahead.toNat<262
  · obtain ⟨used,filledHeap,filledZ,filled,extended,nextOrigin,fillRun,filledState,filledEnd,
      fillAccount,filledBuffers,_startF,_lookF,_agreesF,_stoppedF,fieldsF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have publishF := publish.fill fieldsF
    have pointerF : filledZ.next_out=.ref (.dstate_depth owner) oo := by
      rw [fillAccount.2.2.2.2.2.1,advance_zero]
      exact pointer
    have small : d.lookahead<MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    by_cases wait : (filled.lookahead<MIN_LOOKAHEAD_u && flush==Z_NO_FLUSH)=true
    · have actual : deflate_slow_body (some (.tab ds)) flush st h=.ok ({st with ret:=some need_more},filledHeap) := by
        rw [slow_body_search_decision_source]
        simp only [bind_app,rdD_eq,boundary.good.live.hs,small,ite_true,fillRun,filledState.good.live.hs,wait,ite_true,pure_app]
      have states := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).1
      intro impossible
      rw [← states] at impossible
      cases impossible
    · have notWait := Bool.eq_false_iff.mpr wait
      by_cases empty : filled.lookahead=0
      · have notWaitZero : (decide ((0:UInt32)<MIN_LOOKAHEAD_u) && flush==Z_NO_FLUSH)=false := by simpa only [empty] using notWait
        have actual : deflate_slow_body (some (.tab ds)) flush st h=.ok ({st with brk:=true},filledHeap) := by
          rw [slow_body_search_decision_source]
          simp only [bind_app,rdD_eq,boundary.good.live.hs,small,ite_true,fillRun,filledState.good.live.hs,notWait,Bool.false_eq_true,ite_false,
            empty,notWaitZero,BEq.rfl,ite_true,pure_app]
        have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
        have get := filledState.good.live.hs
        rw [heaps] at get
        have same := Option.some.inj (get.symm.trans live)
        exact fun _ => same ▸ publishF
      · have nonzero : 1≤filled.lookahead.toNat := by
          have nz : filled.lookahead.toNat≠0 := fun zero=>empty (UInt32.toNat_inj.mp zero)
          omega
        have wrapD : d.wrap=1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
        have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
        have suffix : slowSearchDecision (some (.tab ds)) flush st filledHeap=.ok (next,after) := by
          rw [slow_body_search_decision_source] at run
          simpa only [bind_app,rdD_eq,boundary.good.live.hs,small,ite_true,fillRun,filledState.good.live.hs,
            notWait,Bool.false_eq_true,ite_false,beq_eq_false_iff_ne.mpr empty] using run
        exact default_foreign_slow_search_run_ready filledState filledEnd filledBuffers nonzero roomF positive pointerF memory publishF suffix live
  · have ready : 262≤d.lookahead.toNat := by omega
    have room : d.strstart.toNat+262≤d.window_size.toNat := by
      have range:=boundary.range
      dsimp only [fillEnd] at range
      omega
    have suffix := (slow_ready_body_source boundary.good.live.hs ready flush st).symm.trans run
    exact default_foreign_slow_search_run_ready boundary frontier buffers (by omega) room positive pointer memory publish suffix live

end Zlib.Deflate.Engine.Proofs
