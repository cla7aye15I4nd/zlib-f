import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-joint-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-data-environment»
import ZlibF.Proof.«deflate.c.engine.public-dispatch»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual first NO_FLUSH request retains the static environment at every positive
foreign output capacity. No encoding or snapshot premise is needed. -/
theorem public_foreign_first_no_flush_run_static {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (initial : EngineStart h r ds z d) (level : d.level=6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (output : 0<z.avail_out.toNat)
    (memory : config.memory.toNat=16384) (valid : z.avail_in≠0 → z.next_in≠.null)
    (run : deflate (some r) Z_NO_FLUSH h=.ok (rc,after)) : after.static=h.static := by
  have entry := public_default_entry initial (by rw [pointer];intro impossible;cases impossible)
    (by intro zero;rw [zero] at output;contradiction) valid
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD=d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers initial.good buffers Z_NO_FLUSH
  have trees0 := last_flush_trees trees Z_NO_FLUSH
  obtain ⟨headerProduced,middle,zm,dm,_headerWritten,_remaining,headerRun,stateM,goodM,buffersM,accountH,
      _sizesH,_amountH,_countH,statusM,bitsM,_lastM,fieldsM,_headerBytes,_pendingM,_wireM,_adlerM,
      inputH,outputH,_allocH,_nextH,preciseH,shapeH,frameH,_liveH,allocH,nextH⟩ :=
    foreign_zlib_header_buffered_joint_next_physical boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits];decide)
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
  by_cases queued : dm.pending≠0
  · have actual : deflate (some r) Z_NO_FLUSH h=.ok (Z_OK,middle) :=
      entry.trans (by simpa only [bne_iff_ne.mpr queued,ite_true] using headerRun)
    have heaps : middle=after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    subst after
    exact frameH.1.symm
  · have pendingM : dm.pending=0 := Classical.not_not.mp queued
    have actual : deflate (some r) Z_NO_FLUSH h=publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH middle :=
      entry.trans (by simpa only [pendingM,bne_self_eq_false,Bool.false_eq_true,ite_false] using headerRun)
    have readyM : PublishReady dm := ⟨pendingM,stateM.empty_cursor pendingM,by rw [bitsM];decide⟩
    have pointerM : zm.next_out=.ref (.dstate_depth owner) (oo+headerProduced) := by
      rw [accountH.2.2.2.2.2.1,pointer]
      rfl
    have levelM : dm.level=6 := by rw [fieldsM];exact level
    have strategyM : dm.strategy=0 := by rw [fieldsM];exact initial.strategy
    have wrapConfig : config.wrap=1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have dataRun : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH middle=.ok (rc,after) := actual.symm.trans run
    have kept := public_foreign_busy_no_flush_data_run_static stateM buffersM statusM levelM strategyM pointerM memory
      wrapConfig readyM (input_valid_accounting_output valid accountH) dataRun
    exact kept.trans frameH.1.symm

end Zlib.Deflate.Engine.Proofs
