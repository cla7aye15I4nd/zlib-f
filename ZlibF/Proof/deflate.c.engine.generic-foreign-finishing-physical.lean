import ZlibF.Proof.«deflate.c.engine.generic-foreign-trailer-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-finishing-phase»
import ZlibF.Proof.«deflate.c.engine.generic-wrapper-frames»
import ZlibF.Proof.«deflate.c.engine.finishing-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual finishing tail retains counters, full physical storage and its precise
foreign caller byte frame, including a zero-capacity internal trailer publication. -/
theorem public_foreign_finishing_tail_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (empty : z.avail_in=0) (pending : d.pending=0) :
    ∃ produced rc after z' result,
      publicZlibHeader (some r) (some (.tab ds)) (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h=.ok (rc,after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧ z'.total_in=z.total_in ∧
      z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other,pb,buf,trees⟩ := good.trees
    have eq : other=d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨produced,after,z',result,_written,_remaining,run,goodA,_buffersA,account,_sizes,_amount,_left,
      _wrapA,_bitsA,_fields,_bytes,_pendingA,_wire,_adler,inputA,outputA,_alloc,_next,precise,_rest⟩ :=
      foreign_zlib_trailer_publish_encoding good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have physical := foreign_zlib_trailer_run_full_storage good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits run
    have header := public_finishing_header_source good phase empty
    exact ⟨produced,_,after,z',result,header.trans run,goodA,account,inputA,outputA,
      physical.1,physical.2.1,physical.2.2.1,physical.2.2.2.1,physical.2.2.2.2,precise⟩
  · obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
    have precise : BufferFrame h h (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,0⟩] := by
      rw [pointer]
      exact foreign_buffer_frame_of_fields (full_storage_refl h _).2.1 (Shape.refl h) good.uniq get
        (ForeignOwnerFields.refl h owner) rfl (ByteOutputInterval.of_same rfl)
    exact ⟨0,Z_STREAM_END,h,z,d,public_finished_headers good phase.status empty phase.lookahead wrap,
      good,stream_accounting_zero z,rfl,by simp,Shape.refl h,(full_storage_refl h _).2.1,
      full_shape_live_change (Shape.refl h),rfl,rfl,precise⟩

/-- Every accepted positive-capacity finishing-phase public call retains its full physical
storage and precise foreign byte frame. No new input is supplied after FINISH_STATE. -/
theorem public_foreign_finishing_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (empty : z.avail_in=0)
    (output : 0<z.avail_out.toNat) (lower : -2≤d.last_flush.toInt) (upper : d.last_flush.toInt≤5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h=.ok (rc,after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have nonnull : z.next_out≠.null := by rw [pointer];intro impossible;cases impossible
  have positive : z.avail_out≠0 := by intro zero;rw [zero] at output;contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase {d with last_flush:=Z_FINISH} config := phase.control rfl (fun w p => phase.cursor w p)
  have shape0 := shape_setD good.live.hs {d with last_flush:=Z_FINISH}
  have private0 : Frame h (setD h ds {d with last_flush:=Z_FINISH}) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
  have frame0 := full_private_frame_add_output (ob:=owner) private0
  have view0 := private_frame_foreign_output_same good buffers pointer private0
  obtain ⟨foreign,get,_bound,different,_old,_root⟩ := caller_foreign_output good buffers pointer
  by_cases queued : d.pending=0
  · obtain ⟨produced,rc,after,z',result,tailRun,goodA,account,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
      public_foreign_finishing_tail_full_storage_execution good0 buffers0 phase0 pointer empty queued
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
      rw [pointer] at preciseA ⊢
      exact generic_wrapper_foreign_private_prefix private0 view0 preciseA
    exact ⟨produced,rc,after,z',result,entry.trans (source.symm.trans tailRun),goodA,account,inputA,outputA,
      shape0.trans shapeA,full_frame_trans_shape frame0 frameA shape0,
      full_shape_live_change (shape0.trans shapeA),allocA,nextA,precise⟩
  · obtain ⟨before,pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt<8 := by rw [phase.bits];decide
    obtain ⟨_pb,produced,middle,zm,dm,_written,_remaining,pendingBase,flushRun,goodM,buffersM,
      accountM,_sizesM,storageM,amount,pendingCount,_lowM,fields,reset,_bytesM,_pendingM,_bitsM,preciseM⟩ :=
      flush_pending_resume_foreign_bits good0 buffers0 pointer low pending0
    obtain ⟨_adlerM,inputM,outputM,_allocM,_nextM⟩ :=
      flush_pending_low_foreign_run_scalar_effects good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have shapeM := shape0.trans storageM.shape
    have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
    have preciseM' : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
      have wide : BufferFrame (setD h ds {d with last_flush:=Z_FINISH}) middle
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        exact ⟨full_frame_weaken preciseM.1 (fun _ yes => yes.elim Or.inl (fun same => Or.inr (Or.inl same))),preciseM.2⟩
      rw [pointer] at wide ⊢
      exact generic_wrapper_foreign_private_prefix private0 view0 wide
    have moved : 0<produced := by
      rw [amount]
      apply Nat.lt_min.mpr
      refine ⟨?_,output⟩
      have nonzero : d.pending.toNat≠0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      change 0<d.pending.toNat
      omega
    have phaseM : FinishingPhase dm config := by
      apply phase0.control (by rw [fields])
      intro _ emptyM
      exact reset moved (by rw [emptyM];rfl)
    have emptyM : zm.avail_in=0 := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      rw [empty] at count
      exact count
    have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+produced) := by
      rw [accountM.2.2.2.2.2.1,pointer];rfl
    by_cases exhausted : zm.avail_out=0
    · have run := public_pending_finish_exhausted good goodM nonnull positive (by simp [empty]) queued flushRun exhausted
      obtain ⟨middleForeign,middleGet,_⟩ := caller_foreign_output goodM buffersM pointerM
      have precise : BufferFrame h (setD middle ds {dm with last_flush:= -1})
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        rw [pointer] at preciseM' ⊢
        exact generic_wrapper_foreign_setD_frame goodM.live.hs get middleGet different (Or.inr (Or.inl rfl)) rfl preciseM'
      have physical := full_storage_state_trans shapeM frameM storageM.nalloc storageM.nextBlk goodM.live.hs
        (Or.inr (Or.inl (Or.inl rfl))) {dm with last_flush:= -1}
      exact ⟨produced,Z_OK,_,zm,_,run,last_flush_good goodM (-1),accountM,inputM,outputM,
        physical.1,physical.2.1,physical.2.2.1,physical.2.2.2.1,physical.2.2.2.2,precise⟩
    · have noPending : dm.pending=0 := by
        apply UInt64.toNat_inj.mp
        change dm.pending.toNat=0
        have balance := accountM.2.2.2.1
        change produced=min d.pending.toNat z.avail_out.toNat at amount
        change dm.pending.toNat+produced=d.pending.toNat at pendingCount
        have nonzero : zm.avail_out.toNat≠0 := fun zero => exhausted (UInt32.toNat_inj.mp zero)
        omega
      obtain ⟨laterProduced,rc,after,z',result,tailRun,goodA,accountA,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
        public_foreign_finishing_tail_full_storage_execution goodM buffersM phaseM pointerM emptyM noPending
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun exhausted (fun _ => emptyM)
      have owned : DeflateOwned ds dm=DeflateOwned ds d := by rw [fields];rfl
      rw [owned] at frameA preciseA
      have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced+laterProduced⟩] := by
        rw [pointer] at preciseM' ⊢
        rw [pointerM] at preciseA
        exact foreign_buffer_frame_adjacent preciseM' preciseA shapeM shapeA good.uniq get (caller_foreign_owner_outside good buffers pointer)
      have shape := shapeM.trans shapeA
      refine ⟨produced+laterProduced,rc,after,z',result,entry.trans tailRun,goodA,?_,inputA.trans inputM,?_,
        shape,full_frame_trans_shape frameM frameA shapeM,full_shape_live_change shape,
        allocA.trans storageM.nalloc,nextA.trans storageM.nextBlk,precise⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · rw [outputA,outputM,UInt64.ofNat_add,UInt64.add_assoc]

end Zlib.Deflate.Engine.Proofs
