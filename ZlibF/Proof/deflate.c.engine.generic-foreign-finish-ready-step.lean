import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A complete actual prepared FINISH body includes zero entry output capacity.
Source-derived continuation readiness replaces a positive-output premise. -/
theorem default_foreign_slow_finish_ready_step {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null) (st : LoopS) :
    ∃ used produced next after z' result base' ys extended nextOrigin,
      deflate_slow_body (some (.tab ds)) Z_FINISH st h=.ok (next,after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i,i<origin+fillEnd d → extended i=input i) ∧
      nextOrigin+fillEnd result=origin+fillEnd d+used ∧ base≤base' ∧
      (next.ret=some need_more → st.ret=some need_more ∨ z'.avail_out=0) ∧
      (next.ret=st.ret ∨ next.ret=some need_more) ∧
      (next.ret=none → PublishReady result) ∧
      (next.ret=none → next.brk=false → result.lookahead.toNat+z'.avail_in.toNat<d.lookahead.toNat+z.avail_in.toNat) ∧
      (next.brk=true → st.brk=true ∨ (result.lookahead=0 ∧ z'.avail_in=0)) := by
  obtain ⟨used,produced,next,after,z',result,base',ys,extended,nextOrigin,_before,_written,_remaining,
    run,stateA,endA,buffersA,accountA,_length,agrees,endpoint,baseLe,returns,_continues,decrease,breaks,reason,_rest⟩ :=
    default_foreign_slow_body_strategy_encoding boundary frontier buffers positive pointer memory wrap publish inputValid Z_FINISH st
  have ready := default_foreign_slow_body_run_ready_phase boundary frontier buffers positive pointer memory wrap publish inputValid run stateA.good.live.hs
  refine ⟨used,produced,next,after,z',result,base',ys,extended,nextOrigin,run,stateA,endA,buffersA,
    accountA,agrees,endpoint,baseLe,?_,returns,ready,decrease,breaks⟩
  intro returned
  rcases reason returned with old|(⟨impossible,_,_⟩ | empty)
  · exact Or.inl old
  · contradiction
  · exact Or.inr empty

end Zlib.Deflate.Engine.Proofs
