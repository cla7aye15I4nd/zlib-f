import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-no-flush-data»
import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual first NO_FLUSH call retains the initialized working boundary
for every positive legal foreign output capacity, including an exact two-byte
header leaving zero space for the actual strategy dispatch. -/
theorem default_foreign_first_no_flush_buffered {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have state0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers initial.good buffers Z_NO_FLUSH
  obtain ⟨produced,middle,zm,dm,header,stateM,buffersM,accountM,amount,count,statusM,bitsM,lastM,fieldsM⟩ :=
    foreign_zlib_header_buffered state0 (last_flush_trees trees Z_NO_FLUSH) buffers0 pointer
      initial.status initial.wrap initial.strategy initial.windowBits initial.start initial.pending
      initial.pendingOut (by change d.bi_valid.toInt = 0; rw [initial.bits]; rfl) (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
  have entry := public_default_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at output; contradiction) valid
  by_cases waiting : (dm.pending != 0) = true
  · have actual : deflate (some r) Z_NO_FLUSH h = .ok (Z_OK,middle) := by
      rw [entry,header]; simp only [waiting,ite_true]
    have last : dm.last_flush = -1 := by simpa only [waiting,ite_true] using lastM
    exact ⟨0,produced,middle,zm,dm,input,origin,base,[],actual,stateM,buffersM,accountM,statusM,Or.inl last⟩
  · have empty : dm.pending = 0 := by
      by_cases zero : dm.pending = 0
      · exact zero
      · exact False.elim (waiting (bne_iff_ne.mpr zero))
    have ready : PublishReady dm := ⟨empty,stateM.empty_cursor empty,stateM.bits⟩
    have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo+produced) := by
      rw [accountM.2.2.2.2.2.1,pointer]; rfl
    have levelM : dm.level = 6 := by rw [fieldsM]; exact level
    have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact initial.strategy
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    obtain ⟨used,laterProduced,after,z',result,nextInput,nextOrigin,nextBase,ys,run,stateA,buffersA,accountA,statusA,lastA⟩ :=
      default_foreign_public_busy_slow_no_flush_buffered stateM buffersM statusM levelM strategyM pointerM memory wrapConfig ready
        (input_valid_accounting_output valid accountM)
    have previous : dm.last_flush = Z_NO_FLUSH := by
      simpa only [waiting,Bool.false_eq_true,ite_false] using lastM
    rw [previous] at lastA
    refine ⟨used,produced+laterProduced,after,z',result,nextInput,nextOrigin,nextBase,ys,?_,stateA,buffersA,?_,statusA,lastA⟩
    · rw [entry,header]; simpa only [waiting,Bool.false_eq_true,ite_false] using run
    · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
end Zlib.Deflate.Engine.Proofs
