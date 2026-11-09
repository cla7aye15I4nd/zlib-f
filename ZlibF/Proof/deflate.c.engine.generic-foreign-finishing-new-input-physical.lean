import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-physical»
import ZlibF.Proof.«deflate.c.engine.finishing-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A genuine private frame has a precise empty foreign output region. -/
theorem finishing_foreign_private_zero_frame {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (shape : Shape h after)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,0⟩] := by
  obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
  rw [pointer]
  exact foreign_buffer_frame_of_fields (full_frame_weaken frame (fun _ yes => Or.inl yes)) shape good.uniq get
    (ForeignOwnerFields.of_private_frame good buffers pointer frame)
    (ForeignOwnerReadonly.of_private_frame good buffers pointer frame)
    (ByteOutputInterval.of_same (private_frame_foreign_output_same good buffers pointer frame))

/-- New input after FINISH_STATE follows the real pending-first source order. Pending
bytes may exhaust the caller region before refusal. Both returns retain the full caller frame. -/
theorem public_foreign_finishing_new_input_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (valid : z.avail_in≠0 → z.next_in≠.null)
    (nonempty : z.avail_in≠0) (output : 0<z.avail_out.toNat)
    (lower : -2≤d.last_flush.toInt) (upper : d.last_flush.toInt≤5) :
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
  · have source := public_finished_new_input_source good phase.status queued nonnull positive (valid nonempty) nonempty lower upper
    obtain ⟨message,refused⟩ := err_return_run good0.live.hz Z_BUF_ERROR
    let z' := {z with msg:=message}
    have goodA := stream_control_good (z':=z') good0 rfl good.live.zalloc good.live.zfree
    have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
    obtain ⟨shapeE,frameE,_liveE,allocE,nextE⟩ := err_return_run_full_storage good0.live.hz refused
    have shape := shape0.trans shapeE
    have privateAll := full_frame_trans_shape private0
      (full_frame_weaken frameE (fun _ root => Or.inl root)) shape0
    have frame := full_private_frame_add_output (ob:=owner) privateAll
    have precise := finishing_foreign_private_zero_frame good buffers pointer shape privateAll
    exact ⟨0,Z_BUF_ERROR,_,z',_,source.trans refused,goodA,account,rfl,by simp [z'],
      shape,frame,full_shape_live_change shape,allocE,nextE,precise⟩
  · obtain ⟨before,pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt<8 := by rw [phase.bits];decide
    obtain ⟨_pb,produced,middle,zm,dm,_written,_remaining,pendingBase,flushRun,goodM,buffersM,
      accountM,_sizesM,storageM,amount,_pendingCount,_lowM,fields,reset,_bytesM,_pendingM,_bitsM,preciseM⟩ :=
      flush_pending_resume_foreign_bits good0 buffers0 pointer low pending0
    obtain ⟨_adlerM,inputM,outputM,_allocM,_nextM⟩ :=
      flush_pending_low_foreign_run_scalar_effects good0 buffers0 pointer low flushRun goodM.live.hz accountM
    have shapeM := shape0.trans storageM.shape
    have frameM := full_frame_trans_shape frame0 (storageM.private_frame pendingBase) shape0
    have preciseM' : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
      have wide : BufferFrame (setD h ds {d with last_flush:=Z_FINISH}) middle
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] :=
        ⟨full_frame_weaken preciseM.1 (fun _ yes => yes.elim Or.inl (fun same => Or.inr (Or.inl same))),preciseM.2⟩
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
    have inputCount : zm.avail_in=z.avail_in := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      omega
    have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+produced) := by
      rw [accountM.2.2.2.2.2.1,pointer];rfl
    by_cases exhausted : zm.avail_out=0
    · have run := public_pending_finish_exhausted good goodM nonnull positive valid queued flushRun exhausted
      obtain ⟨middleForeign,middleGet,_⟩ := caller_foreign_output goodM buffersM pointerM
      have precise : BufferFrame h (setD middle ds {dm with last_flush:= -1})
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        rw [pointer] at preciseM' ⊢
        exact generic_wrapper_foreign_setD_frame goodM.live.hs get middleGet different (Or.inr (Or.inl rfl)) rfl preciseM'
      have physical := full_storage_state_trans shapeM frameM storageM.nalloc storageM.nextBlk goodM.live.hs
        (Or.inr (Or.inl (Or.inl rfl))) {dm with last_flush:= -1}
      exact ⟨produced,Z_OK,_,zm,_,run,last_flush_good goodM (-1),accountM,inputM,outputM,
        physical.1,physical.2.1,physical.2.2.1,physical.2.2.2.1,physical.2.2.2.2,precise⟩
    · have newInput : zm.avail_in≠0 := by rw [inputCount];exact nonempty
      have source := public_pending_finish_new_input_source good goodM nonnull positive valid queued flushRun exhausted phaseM.status newInput
      obtain ⟨message,refused⟩ := err_return_run goodM.live.hz Z_BUF_ERROR
      let z' := {zm with msg:=message}
      have goodA := stream_control_good (z':=z') goodM rfl goodM.live.zalloc goodM.live.zfree
      have account : StreamAccounting zm z' 0 0 := stream_accounting_zero zm
      obtain ⟨shapeE,frameE,_liveE,allocE,nextE⟩ := err_return_run_full_storage goodM.live.hz refused
      have shape := shapeM.trans shapeE
      have frame := full_frame_trans_shape frameM (full_frame_weaken frameE (fun _ root => Or.inl root)) shapeM
      have privateE : Frame middle (r.put middle z') (fun b => StreamRoot r b ∨ DeflateOwned ds dm b) :=
        full_frame_weaken frameE (fun _ root => Or.inl root)
      have preciseE := finishing_foreign_private_zero_frame goodM buffersM pointerM shapeE privateE
      have owned : DeflateOwned ds dm=DeflateOwned ds d := by rw [fields];rfl
      rw [owned] at preciseE
      have precise : BufferFrame h (r.put middle z') (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        rw [pointer] at preciseM' ⊢
        have regionEq : (⟨zm.next_out,0⟩ : Region)=⟨.ref (.dstate_depth owner) (oo+produced),0⟩ := by rw [pointerM]
        rw [regionEq] at preciseE
        have all := foreign_buffer_frame_adjacent preciseM' preciseE shapeM shapeE good.uniq get
          (caller_foreign_owner_outside good buffers pointer)
        simpa only [Nat.add_zero] using all
      refine ⟨produced,Z_BUF_ERROR,_,z',dm,source.trans refused,goodA,?_,inputM,outputM,
        shape,frame,full_shape_live_change shape,allocE.trans storageM.nalloc,nextE.trans storageM.nextBlk,precise⟩
      simpa only [Nat.zero_add,Nat.add_zero] using stream_accounting_trans accountM account

end Zlib.Deflate.Engine.Proofs
