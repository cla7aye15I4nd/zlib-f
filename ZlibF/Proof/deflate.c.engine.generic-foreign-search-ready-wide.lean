import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual initialized search and decisions retain publication readiness at every output
capacity. The real body cutpoint supplies the explicit comparison room. -/
theorem default_foreign_slow_search_ready_boundary {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1≤d.lookahead.toNat)
    (room : d.strstart.toNat+262≤d.window_size.toNat)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (ready : PublishReady d) (flush : Int32) (st : LoopS) :
    ∃ produced next after z' result base' ys,
      slowSearchDecision (some (.tab ds)) flush st h=.ok (next,after) ∧
      StrategyBoundary after r ds z' result input origin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d.strstart.toNat<result.strstart.toNat ∧ result.lookahead.toNat<d.lookahead.toNat ∧
      fillEnd result=fillEnd d ∧ base≤base' ∧ next.brk=st.brk ∧
      (next.ret=st.ret ∨ next.ret=some need_more) ∧
      (next.ret=some need_more → st.ret=some need_more ∨ z'.avail_out=0) ∧
      (next.ret=none → PublishReady result) ∧
      (0<z.avail_out.toNat → next.ret=none → 0<z'.avail_out.toNat) := by
  obtain ⟨produced,next,after,z',result,base',ys,_before,_written,_remaining,run,stateA,endA,buffersA,
    accountA,_length,progress,less,endpoint,baseLe,brk,returns,reason,continues,_rest⟩ :=
    default_foreign_slow_search_decision_strategy_encoding boundary frontier buffers lookahead room positive pointer memory ready flush st
  have readyA := default_foreign_slow_search_run_ready boundary frontier buffers lookahead room positive pointer memory ready run stateA.good.live.hs
  exact ⟨produced,next,after,z',result,base',ys,run,stateA,endA,buffersA,accountA,
    progress,less,endpoint,baseLe,brk,returns,reason,readyA,continues⟩

end Zlib.Deflate.Engine.Proofs
