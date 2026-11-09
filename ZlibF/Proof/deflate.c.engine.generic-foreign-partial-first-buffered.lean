import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-data-safety»
import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.strategy-no-flush-loop»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real first PARTIAL1 call retains the initialized working
protocol for every positive caller capacity. Split headers and exact-two-byte
headers are included; no encoding history or callee contract is assumed. -/
theorem public_foreign_first_partial_buffered {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH) :
    ∃ used produced after z' result extended nextOrigin nextBase ys,
      deflate (some r) flush h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status=BUSY_STATE ∧
      (result.last_flush=flush ∨ result.last_flush= -1) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have flagLo : 0≤flush.toInt := by rw [flag];decide
  have flagHi : flush.toInt≤5 := by rw [flag];decide
  have entry := public_default_valid_initial_entry initial nonnull positive valid flush flagLo flagHi
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0 := last_flush_buffered_boundary boundary flush
  have trees0 := last_flush_trees trees flush
  have buffers0 := last_flush_buffers initial.good buffers flush
  obtain ⟨headerProduced, middle, zm, dm, headerRun, stateM, buffersM, accountM, _amountM,
      _pendingCountM, statusM, bitsM, lastM, fieldsM⟩ :=
    foreign_zlib_header_buffered boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits]; decide)
      (publicDataTail (some r) (some (.tab ds)) flush)
  by_cases queued : dm.pending = 0
  · have headerActual : publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) flush)
        (setD h ds {d with last_flush := flush}) =
        publicDataTail (some r) (some (.tab ds)) flush middle := by
      simpa only [queued, bne_self_eq_false, Bool.false_eq_true, ite_false] using headerRun
    have publish : PublishReady dm := ⟨queued, stateM.empty_cursor queued, by rw [bitsM]; decide⟩
    have levelM : dm.level = 6 := by rw [fieldsM]; exact level
    have strategyM : dm.strategy = 0 := by rw [fieldsM]; exact initial.strategy
    have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + headerProduced) := by
      rw [accountM.2.2.2.2.2.1, pointer]; rfl
    have wrapConfig : config.wrap = 1 :=
      (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    obtain ⟨used,laterProduced,after,z',result,extended,nextOrigin,nextBase,ys,dataRun,stateA,buffersA,
        accountA,statusA,lastA⟩ :=
      public_foreign_busy_partial_data_safety stateM buffersM statusM levelM strategyM pointerM memory
        wrapConfig publish (input_valid_accounting_output valid accountM) flush flag
    have lastHeader : dm.last_flush = flush := by simpa [queued] using lastM
    rw [lastHeader] at lastA
    refine ⟨used,headerProduced+laterProduced,after,z',result,extended,nextOrigin,nextBase,ys,
      entry.trans (headerActual.trans dataRun),stateA,buffersA,?_,statusA,?_⟩
    · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
    · exact lastA.elim (fun same=>Or.inl same) (fun retry=>Or.inr retry)
  · have headerActual : publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) flush)
        (setD h ds {d with last_flush := flush}) = .ok (Z_OK, middle) := by
      simpa [queued] using headerRun
    have lastHeader : dm.last_flush = -1 := by simpa [queued] using lastM
    exact ⟨0,headerProduced,middle,zm,dm,input,origin,base,[],entry.trans headerActual,stateM,
      buffersM,accountM,statusM,Or.inr lastHeader⟩

end Zlib.Deflate.Engine.Proofs
