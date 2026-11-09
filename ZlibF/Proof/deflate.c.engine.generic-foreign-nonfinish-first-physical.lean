import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-joint-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-data-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»
import ZlibF.Proof.«deflate.c.engine.public-first-full-storage»
import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual first non-FINISH call retains its complete physical effects and exact caller
byte frame at every positive capacity, including one and exactly two header bytes. -/
theorem public_foreign_first_nonfinish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level=6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (output : 0<z.avail_out.toNat)
    (memory : config.memory.toNat=16384) (valid : z.avail_in≠0 → z.next_in≠.null)
    (flush : Int32) (flag : flush=Z_NO_FLUSH ∨ flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h=.ok (rc,after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' used produced ∧ z'.total_in=z.total_in+UInt64.ofNat used ∧
      z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have entry := public_default_valid_initial_entry initial (by rw [pointer];intro impossible;cases impossible)
    (by intro zero;rw [zero] at output;contradiction) valid flush
      (by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide) (by rcases flag with rfl|rfl|rfl|rfl|rfl <;> decide)
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD=d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers initial.good buffers flush
  have trees0 := last_flush_trees trees flush
  have shape0 := shape_setD initial.good.live.hs {d with last_flush:=flush}
  have private0 : Frame h (setD h ds {d with last_flush:=flush}) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
  have frame0 := full_private_frame_add_output (ob:=owner) private0
  have view0 := private_frame_foreign_output_same initial.good buffers pointer private0
  obtain ⟨headerProduced,middle,zm,dm,_headerWritten,_remaining,headerRun,stateM,goodM,buffersM,accountH,
      _sizesH,_amountH,_countH,statusM,bitsM,_lastM,fieldsM,_headerBytes,_pendingM,_wireM,_adlerM,
      inputH,outputH,_allocH,_nextH,preciseH,shapeH,frameH,_liveH,allocH,nextH⟩ :=
    foreign_zlib_header_buffered_joint_next_physical boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits];decide)
      (publicDataTail (some r) (some (.tab ds)) flush)
  have shapeHeader := shape0.trans shapeH
  have frameHeader := full_frame_trans_shape frame0 frameH shape0
  have preciseHeader : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,headerProduced⟩] := by
    rw [pointer] at preciseH ⊢
    exact generic_wrapper_foreign_private_prefix private0 view0 preciseH
  by_cases queued : dm.pending≠0
  · have actual : deflate (some r) flush h=.ok (Z_OK,middle) :=
      entry.trans (by simpa only [bne_iff_ne.mpr queued,ite_true] using headerRun)
    refine ⟨0,headerProduced,Z_OK,middle,zm,dm,actual,goodM,accountH,?_,outputH,
      shapeHeader,frameHeader,full_shape_live_change shapeHeader,allocH,nextH,preciseHeader⟩
    change zm.total_in=z.total_in+0
    simpa only [UInt64.add_zero] using inputH
  · have pendingM : dm.pending=0 := Classical.not_not.mp queued
    have actual : deflate (some r) flush h=publicDataTail (some r) (some (.tab ds)) flush middle :=
      entry.trans (by simpa only [pendingM,bne_self_eq_false,Bool.false_eq_true,ite_false] using headerRun)
    have readyM : PublishReady dm := ⟨pendingM,stateM.empty_cursor pendingM,by rw [bitsM];decide⟩
    have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+headerProduced) := by
      rw [accountH.2.2.2.2.2.1,pointer]
      rfl
    have levelM : dm.level=6 := by rw [fieldsM];exact level
    have strategyM : dm.strategy=0 := by rw [fieldsM];exact initial.strategy
    have wrapConfig : config.wrap=1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    obtain ⟨used,produced,after,z',result,_nextInput,_nextOrigin,_nextBase,_ys,dataRun,stateA,_buffersA,accountA,
        _statusA,_lastA,inputA,outputA,shapeA,frameA,_liveA,allocA,nextA,preciseA⟩ :=
      public_foreign_busy_nonfinish_data_full_storage_execution stateM buffersM statusM levelM strategyM pointerM memory
        wrapConfig readyM (input_valid_accounting_output valid accountH) flush flag
    have goodA := stateA.good
    have owned : DeflateOwned ds dm=DeflateOwned ds d :=
      (show ConfigFrame d dm from stateM.configuration.trans boundary.configuration.symm).owned (ds:=ds)
    rw [owned] at frameA preciseA
    have shape := shapeHeader.trans shapeA
    have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,headerProduced+produced⟩] := by
      obtain ⟨foreign,get,_⟩ := caller_foreign_output initial.good buffers pointer
      rw [pointer] at preciseHeader ⊢
      rw [pointerM] at preciseA
      exact foreign_buffer_frame_adjacent preciseHeader preciseA shapeHeader shapeA initial.good.uniq get
        (caller_foreign_owner_outside initial.good buffers pointer)
    refine ⟨used,headerProduced+produced,Z_OK,after,z',result,actual.trans dataRun,goodA,?_,?_,?_,
      shape,full_frame_trans_shape frameHeader frameA shapeHeader,full_shape_live_change shape,
      allocA.trans allocH,nextA.trans nextH,precise⟩
    · simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA
    · rw [inputA,inputH]
    · rw [outputA,outputH,UInt64.ofNat_add,UInt64.add_assoc]

end Zlib.Deflate.Engine.Proofs
