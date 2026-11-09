import ZlibF.Proof.«deflate.c.engine.generic-foreign-final-tail-effects»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-eof-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real EOF literal settlement and insertion reset precede final publication.
The exact same actual EOF run retains Adler and has exact wrapping totals. -/
theorem default_foreign_slow_eof_finish_effect_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (wrap : d.wrap=1) :
    ∃ produced ret after z' result,
      slowEofTail (some (.tab ds)) Z_FINISH h=.ok (ret,after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in=z.total_in ∧
      z'.total_out=z.total_out+UInt64.ofNat produced ∧ z'.adler=z.adler := by
  obtain ⟨settledHeap,settled,ys,settleRun,settledBoundary,settledFrontier,settledBuffers,
    settledFlag,settledLook,_settledStart,_settledCount,settledClear,settledConfig,settledFrame,_symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted:=eofInsert settled
  obtain ⟨insertRun,insertedBoundary,insertedFrontier,insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds inserted)
    (fun k equal=>(stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have configI : ConfigFrame d inserted:=settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear inserted:=⟨settledClear.bl,settledClear.opt,settledClear.fixed⟩
  have bitsI : inserted.bi_valid.toInt≤7 := by
    change settled.bi_valid.toInt≤7
    have bitFrame : settled.bi_valid=d.bi_valid := by rw [settledFrame]
    rw [bitFrame]
    have low:=boundary.bits
    omega
  obtain ⟨produced,ret,after,z',result,tailRun,goodA,accountA,inputA,outputA,checksumA⟩ :=
    default_foreign_finish_tail_effect_execution insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level];exact positive) pointer
      (by change settled.pending_out=settled.pending_buf;rw [settledFrame];exact cursor)
      (by rw [configI.memory];exact memory)
      (by change settled.pending=0;rw [settledFrame];exact pending) bitsI clearI settledFlag
      (by rw [configI.wrap];exact wrap)
  refine ⟨produced,ret,after,z',result,?_,goodA,accountA,inputA,outputA,checksumA⟩
  unfold slowEofTail
  rw [bind_app,settleRun]
  simp only []
  rw [bind_app,insertRun]
  exact tailRun

/-- Every presentation of the same actual EOF return has exact wrapping totals.
The domain is the tracked EOF refinement with only the caller pointer variant changed. -/
theorem default_foreign_slow_eof_finish_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (wrap : d.wrap=1)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h=.ok (ret,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned 0 produced) :
    returned.total_in=z.total_in ∧ returned.total_out=z.total_out+UInt64.ofNat produced := by
  obtain ⟨amount,_otherRet,other,otherZ,_otherD,actual,goodA,accountA,inputA,outputA,_checksumA⟩ :=
    default_foreign_slow_eof_finish_effect_execution boundary frontier buffers empty positive pointer cursor memory pending wrap
  have same:=actual_run_stream_unique actual run goodA.live.hz live
  rw [same] at accountA inputA outputA
  have count : produced=amount := (stream_accounting_counts_unique account accountA).2
  exact ⟨inputA,count ▸ outputA⟩

/-- Every presentation of the same actual EOF return preserves Adler.
No positive-output or callee checksum premise is introduced. -/
theorem default_foreign_slow_eof_finish_run_adler {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (wrap : d.wrap=1)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h=.ok (ret,after)) (live : r.get after=some returned)
    (account : StreamAccounting z returned 0 produced) : returned.adler=z.adler := by
  obtain ⟨_amount,_otherRet,other,otherZ,_otherD,actual,goodA,_accountA,_inputA,_outputA,checksumA⟩ :=
    default_foreign_slow_eof_finish_effect_execution boundary frontier buffers empty positive pointer cursor memory pending wrap
  have same:=actual_run_stream_unique actual run goodA.live.hz live
  exact same ▸ checksumA

end Zlib.Deflate.Engine.Proofs
