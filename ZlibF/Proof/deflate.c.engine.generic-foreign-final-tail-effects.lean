import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-tail»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual final publication and its control reads preserve Adler and have exact totals.
The explicit earlier EOF frontier is supplied by the real EOF settlement/insert stages.
All caller output capacities, including zero, are included. -/
theorem default_foreign_finish_tail_effect_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0) (wrap : d.wrap=1) :
    ∃ produced ret after z' result,
      finish_tail (some (.tab ds)) Z_FINISH h=.ok (ret,after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in=z.total_in ∧
      z'.total_out=z.total_out+UInt64.ofNat produced ∧ z'.adler=z.adler := by
  obtain ⟨produced,after,z',result,_before,_written,_remaining,_kind,_body,_padding,
    macroRun,stateA,_endA,_buffersA,accountA,_clearA,frameA,_rest⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available true
  have wrapA : result.wrap=1 := by rw [frameA];exact wrap
  have macroRun1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h=.ok ((),after) := macroRun
  have controlRun : FLUSH_BLOCK (some (.tab ds)) 1 h=
      .ok ((if z'.avail_out==0 then some finish_started else none),after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app,macroRun1,ldDeflateState_tab stateA.good.live.hs,stateA.good.live.back,zrd_eq,stateA.good.live.hz]
    by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app,wrapA]
  have counts := default_foreign_flush_control_run_counter_effects boundary buffers positive pointer cursor memory pending bits clear available true
    controlRun stateA.good.live.hz accountA
  have checksum := default_foreign_flush_control_run_adler boundary buffers positive pointer cursor memory pending bits clear available true
    controlRun stateA.good.live.hz accountA
  refine ⟨produced,if z'.avail_out==0 then finish_started else finish_done,after,z',result,?_,stateA.good,accountA,counts.1,counts.2,checksum⟩
  unfold finish_tail
  simp only [beq_self_eq_true,ite_true,bind_app,controlRun]
  by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app]

/-- The same actual final-tail return has exact wrapping input/output totals. -/
theorem default_foreign_finish_tail_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0) (wrap : d.wrap=1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h=.ok (ret,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned 0 produced) :
    returned.total_in=z.total_in ∧ returned.total_out=z.total_out+UInt64.ofNat produced := by
  obtain ⟨amount,otherRet,other,otherZ,_otherD,actual,goodA,accountA,inputA,outputA,_checksumA⟩ :=
    default_foreign_finish_tail_effect_execution boundary frontier buffers positive pointer cursor memory pending bits clear available wrap
  have same := actual_run_stream_unique actual run goodA.live.hz live
  rw [same] at accountA inputA outputA
  have count : produced=amount := (stream_accounting_counts_unique account accountA).2
  exact ⟨inputA,count ▸ outputA⟩

/-- The same actual final-tail return retains Adler without a callee checksum premise. -/
theorem default_foreign_finish_tail_run_adler {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0) (wrap : d.wrap=1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h=.ok (ret,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned 0 produced) : returned.adler=z.adler := by
  obtain ⟨_amount,_otherRet,other,otherZ,_otherD,actual,goodA,_accountA,_inputA,_outputA,checksumA⟩ :=
    default_foreign_finish_tail_effect_execution boundary frontier buffers positive pointer cursor memory pending bits clear available wrap
  have same := actual_run_stream_unique actual run goodA.live.hz live
  exact same ▸ checksumA

end Zlib.Deflate.Engine.Proofs
