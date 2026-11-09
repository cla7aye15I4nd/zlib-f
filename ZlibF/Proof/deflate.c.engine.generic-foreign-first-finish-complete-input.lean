import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-data-completed»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered-joint-next»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-data-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-complete-encoding»

/-! # The actual first complete-header FINISH call encodes its original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The actual first FINISH call writes its default header and executes
the entire strategy and trailer path, including exactly two output bytes.
Encoding and checksum are established from actual initialized fields.
The accepted input is exactly the consumed original caller snapshot.
Split headers and entry refusals have their separate source branches. -/
theorem public_foreign_first_finish_complete_encoding {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (room : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result rawWritten accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (2 + rawWritten.length) ∧
      Bytes after z.next_out (2 + rawWritten.length) ([120,156] ++ rawWritten) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase rawWritten ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ FinishedEncoding after result accepted rawWritten)) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ rawWritten)) := by
  have entry := public_default_finish_initial_entry initial
    (by rw [pointer];intro impossible;cases impossible)
    (by intro zero;rw [zero] at room;change 2≤0 at room;omega) valid
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD=d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0:=last_flush_buffered_boundary boundary Z_FINISH
  have buffers0:=last_flush_buffers initial.good buffers Z_FINISH
  have trees0:=last_flush_trees trees Z_FINISH
  obtain ⟨headerProduced,middle,zm,dm,headerWritten,remaining,⟨headerRun,stateM,_goodM,buffersM,accountM,
      _sizes,amount,count,statusM,bitsM,_lastM,fieldsM,headerBytes,pendingM,wireM,adlerM,_inM,_outM,_allocM,_nextM,preciseM⟩,borrowM⟩ :=
    foreign_zlib_header_buffered_joint_next_borrow boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits];decide)
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
  have amountTwo : headerProduced=2 := amount.trans (Nat.min_eq_left room)
  rw [amountTwo] at accountM count headerBytes preciseM
  have drained : dm.pending=0 := UInt64.toNat_inj.mp (by change dm.pending.toNat=0;omega)
  have headerActual : deflate (some r) Z_FINISH h=publicDataTail (some r) (some (.tab ds)) Z_FINISH middle :=
    entry.trans (by simpa only [drained,bne_self_eq_false,Bool.false_eq_true,ite_false] using headerRun)
  have readyM : PublishReady dm:=⟨drained,stateM.empty_cursor drained,by rw [bitsM];decide⟩
  have remainingNil : remaining=[] := pending_bits_empty pendingM (by rw [drained];rfl) (by rw [bitsM];rfl)
  have header : levelHeaderPrefix d.level=[120,156] := by rw [level];decide
  have writtenEq : headerWritten=[120,156] := by
    apply encoded_bytes_injective
    simpa only [remainingNil,List.append_nil,header] using wireM
  rw [writtenEq] at headerBytes
  have prefixEmpty : inputPrefix input (0+fillEnd dm)=[] := by
    have startM : dm.strstart=0 := by rw [fieldsM];exact initial.start
    have lookM : dm.lookahead=0 := by rw [fieldsM];exact initial.lookahead
    simp only [fillEnd,startM,lookM,UInt32.toNat_zero,Nat.add_zero,inputPrefix,List.range_zero,List.map_nil]
  have encodingM : RawPrefix middle dm input 0 [] := by
    refine ⟨[],[],remainingNil ▸ pendingM,rfl,?_⟩
    simpa only [inputPrefix,List.range_zero,List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0
  have checksumM : zm.adler=(ZlibF.Spec.adler32 (inputPrefix input (0+fillEnd dm))).toUInt64 := by
    simpa only [prefixEmpty,show (ZlibF.Spec.adler32 []).toUInt64=(1:UInt64) from by decide] using adlerM
  have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+2) := by
    rw [accountM.2.2.2.2.2.1,pointer]
    rfl
  have levelM : dm.level=6 := by rw [fieldsM];exact level
  have strategyM : dm.strategy=0 := by rw [fieldsM];exact initial.strategy
  have wrapConfig : config.wrap=1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have snapshot0:=caller_bytes_setD_depth (result:={d with last_flush:=Z_FINISH}) initial.good.live.hs rfl snapshot
  have snapshotM : Bytes middle zm.next_in zm.avail_in.toNat actualInput := by
    have originalBuffers:=buffers0
    obtain ⟨oldZ,oldGet,inputRange,_outputRange,separated⟩ := originalBuffers
    have oldEq : oldZ=z := Option.some.inj (oldGet.symm.trans boundary0.good.live.hz)
    subst oldZ
    have separateNow : Separate z.next_in z.avail_in.toNat z.next_out 2 := by
      simpa only [advance_zero] using separate_advance_right (used:=0) separated room
    have kept:=foreign_caller_input_bytes_preserved boundary0.good buffers0 pointer inputRange separateNow
      (Nat.le_refl _) snapshot0 preciseM borrowM
    have inputPointer : zm.next_in=z.next_in := by simpa only [advance_zero] using accountM.2.2.2.2.1
    have inputCount : zm.avail_in=z.avail_in := UInt32.toNat_inj.mp (by have count:=accountM.2.2.1;omega)
    rw [inputPointer,inputCount]
    exact kept
  obtain ⟨used,rc,after,z',result,rawWritten,accepted,acceptedA,dataRun,goodA,buffersA,
      accountA,bytesA,checksumA,phasesA,endedA⟩ :=
    public_foreign_busy_finish_data_completed_encoding stateM buffersM statusM levelM strategyM pointerM memory
      wrapConfig readyM (input_valid_accounting_output valid accountM) snapshotM checksumM encodingM
  have acceptedEq : accepted=actualInput.take used := by simpa only [prefixEmpty,List.nil_append] using acceptedA
  have effect:=public_foreign_busy_finish_data_run_output_interval stateM buffersM statusM levelM strategyM pointerM
    memory wrapConfig readyM (input_valid_accounting_output valid accountM) dataRun goodA.live.hz accountA
  have earlier : Bytes after (.ref (.dstate_depth owner) oo) 2 [120,156] := by
    rw [pointer] at headerBytes
    exact effect.keep_published_bytes headerBytes
  have current : Bytes after (.ref (.dstate_depth owner) (oo+2)) rawWritten.length rawWritten := by
    rw [pointerM] at bytesA
    exact bytesA
  have combined:=generic_published_bytes_append earlier current
  have account : StreamAccounting z z' used (2+rawWritten.length) := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
  refine ⟨used,rc,after,z',result,rawWritten,accepted,acceptedEq,headerActual.trans dataRun,
    goodA,buffersA,account,?_,checksumA,?_,?_⟩
  · rw [pointer]
    exact combined
  · simpa only [List.nil_append] using phasesA
  · intro ended
    simpa only [List.append_nil] using endedA ended

end Zlib.Deflate.Engine.Proofs
