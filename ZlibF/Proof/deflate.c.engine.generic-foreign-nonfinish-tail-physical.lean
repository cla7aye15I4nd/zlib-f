import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-call»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-eof-prefix»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-whole-counters»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Exact counters and complete object frame of the actual nonfinal tail. -/
theorem foreign_nonfinal_tail_run_physical {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0<d.level.toInt)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0) (bits : d.bi_valid.toInt≤7)
    (clear : BlockInit.BlockClear d) (available : d.match_available=0)
    (flush : Int32) (nonfinal : flush≠Z_FINISH)
    (run : finish_tail (some (.tab ds)) flush h=.ok (ret,after))
    (live : r.get after=some z') (account : StreamAccounting z z' 0 produced) :
    z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
    Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
    LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  by_cases empty : d.sym_next=0
  · have actual : finish_tail (some (.tab ds)) flush h=.ok (block_done,h) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal,Bool.false_eq_true,ite_false,
        bind_app,rdD_eq,boundary.good.live.hs,empty,bne_self_eq_false,pure_app]
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst after
    have streams : z=z' := Option.some.inj (boundary.good.live.hz.symm.trans live)
    subst z'
    have count := (stream_accounting_counts_unique account (stream_accounting_zero z)).2
    subst produced
    exact ⟨rfl,by simp,full_storage_refl h _⟩
  · obtain ⟨amount,other,otherZ,otherD,macroRun,stateA,_buffersA,accountA,_clearA,_fields,_lowA,_readyA,_controlsA⟩ :=
      default_foreign_flush_nonfinal_loop_boundary boundary frontier buffers positive pointer cursor memory pending bits clear available
    have actual : finish_tail (some (.tab ds)) flush h=
        .ok ((if otherZ.avail_out==0 then need_more else block_done),other) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal,Bool.false_eq_true,ite_false,
        bind_app,rdD_eq,boundary.good.live.hs,bne_iff_ne.mpr empty,ite_true,macroRun]
      by_cases exhausted : (otherZ.avail_out==0)=true <;> simp [exhausted,pure_app]
    have storage := default_foreign_flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available false macroRun
    have counts := default_foreign_flush_control_run_counter_effects boundary buffers positive pointer cursor memory pending bits clear available false
      macroRun stateA.good.live.hz accountA
    have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst after
    have streams : otherZ=z' := Option.some.inj (stateA.good.live.hz.symm.trans live)
    subst z'
    have count := (stream_accounting_counts_unique accountA account).2
    rw [count] at counts
    exact ⟨counts.1,counts.2,storage⟩

/-- The actual nonfinal EOF settlement, insertion and publication preserve the full physical frame. -/
theorem foreign_nonfinal_eof_run_physical {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0)
    (positive : 0<d.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (cursor : d.pending_out=d.pending_buf) (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0)
    (flush : Int32) (nonfinal : flush≠Z_FINISH)
    (run : slowEofTail (some (.tab ds)) flush h=.ok (ret,after))
    (live : r.get after=some z') (account : StreamAccounting z z' 0 produced) :
    z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
    Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
    LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  obtain ⟨settledHeap,settled,ys,settleRun,settledBoundary,settledFrontier,settledBuffers,
      settledFlag,settledLook,_settledStart,_settledCount,settledClear,settledConfig,settledFrame,_symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  obtain ⟨insertRun,insertedBoundary,insertedFrontier,insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds inserted)
    (fun k equal=>(stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have configI : ConfigFrame d inserted := settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear inserted := ⟨settledClear.bl,settledClear.opt,settledClear.fixed⟩
  have bitsI : inserted.bi_valid.toInt≤7 := by
    change settled.bi_valid.toInt≤7
    have eq : settled.bi_valid=d.bi_valid := by rw [settledFrame]
    rw [eq]
    have low := boundary.bits
    omega
  obtain ⟨amount,otherRet,other,otherZ,otherD,tailRun,contentA,_buffersA,accountA,_rest⟩ :=
    default_foreign_finish_tail_nonfinal_boundary insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level];exact positive) pointer
      (by change settled.pending_out=settled.pending_buf;rw [settledFrame];exact cursor)
      (by rw [configI.memory];exact memory)
      (by change settled.pending=0;rw [settledFrame];exact pending) bitsI clearI settledFlag flush nonfinal
  have actual : slowEofTail (some (.tab ds)) flush h=.ok (otherRet,other) := by
    unfold slowEofTail
    rw [bind_app,settleRun]
    simp only []
    rw [bind_app,insertRun]
    exact tailRun
  obtain ⟨inputT,outputT,shapeT,frameT,_liveT,allocT,nextT⟩ :=
    foreign_nonfinal_tail_run_physical insertedBoundary insertedFrontier insertedBuffers
      (by rw [configI.level];exact positive) pointer
      (by change settled.pending_out=settled.pending_buf;rw [settledFrame];exact cursor)
      (by rw [configI.memory];exact memory)
      (by change settled.pending=0;rw [settledFrame];exact pending) bitsI clearI settledFlag flush nonfinal tailRun contentA.good.live.hz accountA
  obtain ⟨shapeS,frameS,_liveS,allocS,nextS⟩ := slow_eof_literal_run_full_storage boundary.toContentBoundary boundary.strict settleRun
  have shapeI := shape_setD settledBoundary.good.live.hs inserted
  have frameI : Frame settledHeap (setD settledHeap ds inserted) (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) :=
    full_frame_weaken (state_store_full_frame settledHeap ds inserted) (fun _ same=>Or.inr (Or.inl (Or.inl same)))
  rw [configI.owned (ds:=ds)] at frameT
  have shape := (shapeS.trans shapeI).trans shapeT
  have frame := full_frame_trans_shape
    (full_frame_trans_shape (full_private_frame_add_output frameS) frameI shapeS) frameT (shapeS.trans shapeI)
  have storage := And.intro shape (And.intro frame (And.intro (full_shape_live_change shape) (And.intro (allocT.trans allocS) (nextT.trans nextS))))
  have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst after
  have streams : otherZ=z' := Option.some.inj (contentA.good.live.hz.symm.trans live)
  subst z'
  have count := (stream_accounting_counts_unique accountA account).2
  rw [count] at outputT
  exact ⟨inputT,outputT,storage⟩

/-- The pure EOF prefix producer supplies its actual full byte frame without an encoding premise. -/
theorem foreign_nonfinal_eof_run_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead=0)
    (positive : 0<d.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (cursor : d.pending_out=d.pending_buf) (memory : d.lit_bufsize.toNat=16384) (pending : d.pending=0)
    (flush : Int32) (nonfinal : flush≠Z_FINISH)
    (run : slowEofTail (some (.tab ds)) flush h=.ok (ret,after))
    (live : r.get after=some z') (account : StreamAccounting z z' 0 produced) :
    BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨amount,otherRet,other,otherZ,otherD,_ys,_before,_written,_remaining,_bits,actual,contentA,_end,_buffers,accountA,
      _clear,_config,_look,_start,_available,_insert,_low,_ready,_symbols,_pending,_bytes,_remainingA,
      _wire,_meaning,_position,_returns,_exhausted,_adler,_shape,precise⟩ :=
    default_foreign_slow_eof_nonfinal_block_prefix boundary frontier buffers empty positive pointer cursor memory pending
      (offset:=d.bi_valid.toInt.toNat) rfl flush nonfinal
  have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst after
  have streams : otherZ=z' := Option.some.inj (contentA.good.live.hz.symm.trans live)
  rw [streams] at accountA
  have count := (stream_accounting_counts_unique accountA account).2
  exact count ▸ precise
end Zlib.Deflate.Engine.Proofs
