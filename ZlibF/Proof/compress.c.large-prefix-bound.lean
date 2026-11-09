import ZlibF.Proof.«compress.c.small-bound»
import ZlibF.Proof.«compress.c.bound-source-size»
import ZlibF.Proof.«deflate.c.engine.counted-request»

/-! # Count the actual large-source utility loop

The cumulative metadata comes from the proved actual default initializer
and actual requests. The finite-prefix induction establishes every real
wrapper guard. No callee contract or request guard is assumed by the final
wrapper consumer. The original Uniq/raw-output internal scope is explicit.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLarge
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressLoop
open ZlibF.Spec.Public.Proofs.CompressPrefix ZlibF.Spec.Public.Proofs.CompressTail
open ZlibF.Spec.Public.Proofs.CompressMemory ZlibF.Spec.Public.Proofs.CompressModes
open ZlibF.Spec.Public.Proofs.CompressBuffer ZlibF.Spec.Public.Proofs.CompressSmall
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem zero_execution {slot : Nat} {start after : Heap} {first last : Locals}
    (execution : ActualPrefix slot start first 0 after last) : after = start ∧ last = first := by
  cases execution
  exact ⟨rfl,rfl⟩

private theorem prepare_empty_input (h : Heap) (slot : Nat) (z : ZStream) (left : UInt64) :
    (prepare h slot z left 0).2.1 = 0 := by
  have zero : CompressChunks.chunk (0 : UInt64) = 0 := by decide +kernel
  simp only [prepare,zero,show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl]
  split <;>rfl

/-- Every adequate-capacity prefix of the real large-source loop retains
actual cumulative metadata, the exact caller trace/counts and only OK/END
codes. The two header bytes, positive offers and post-final no-input guard
are derived from the actual wrapper execution here. -/
theorem large_prefix_counted {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {initialD : DeflateState} {config : EngineConfig}
    {capacity pending : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : CountedBoundary start (.tab slot) ds first initialD config 0 0)
    (globals : LibraryGlobals start) (ranges : Ranges start (.tab slot) first capacity pending source)
    (pointer : first.next_out = .ref (.blk ob) oo) (outZero : first.avail_out = 0)
    (notFinished : initialD.status ≠ FINISH_STATE)
    (object : source.length < 2^63) (large : 33554432 ≤ source.length)
    (room : Api.compressBound source.length ≤ capacity.toNat)
    (execution : ActualPrefix slot start (Z_OK,capacity,pending) k after last) :
    ∃ used log za da,
      PrefixAccount slot first capacity pending source k after last used log za ∧
      CountedBoundary after (.tab slot) ds za da config used log.output.length ∧
      (last.1 = Z_OK ∨ last.1 = Z_STREAM_END) ∧
      (0 < k → da.status = BUSY_STATE ∨ da.status = FINISH_STATE) := by
  induction execution with
  | nil =>
    obtain ⟨used,log,za,sound⟩ := actual_prefix_sound history initial.protocol.good.live.hz ranges pointer ActualPrefix.nil
    have same : za = first := Option.some.inj (sound.get.symm.trans initial.protocol.good.live.hz)
    subst za
    have emptyInput : used = 0 := by have counts := sound.inputCount;dsimp only at counts;omega
    have emptyOutput : log.output.length = 0 := by have counts := sound.outputCount;dsimp only at counts;omega
    refine ⟨used,log,first,initialD,sound,?_,Or.inl rfl,fun positive => by omega⟩
    rw [emptyInput,emptyOutput]
    exact initial
  | @step k h after current next previous guard actual ih =>
    obtain ⟨already,oldLog,z,d,known,counted,_oldAllowed,oldStatus⟩ := ih
    rcases current with ⟨old,l,n⟩
    have frame := prefix_frame history initial.protocol ranges pointer previous
    have currentGlobals : LibraryGlobals h := frame.1.symm.trans globals
    have raw : z.next_out = .ref (.blk ob) (oo+oldLog.output.length) := by rw [known.outputPtr,pointer];rfl
    have strict := counted.written_compress_bound_strict known.usedBound object large
    have budget := known.outputCount
    dsimp only at budget
    rw [outZero,UInt32.toNat_zero,Nat.zero_add] at budget
    have positive : 0 < (CompressLoop.preparedStream z l n).avail_out.toNat :=
      prepare_output_positive z l n (by omega)
    have edit := prepare_rebuffer counted.protocol.good currentGlobals l n
    obtain ⟨zp,getP,countedP⟩ := counted.rebuffer edit
    have sameP : zp = CompressLoop.preparedStream z l n :=
      Option.some.inj (getP.symm.trans (prepare_get h slot z l n known.get))
    subst zp
    have rangesP := prepare_ranges counted.protocol.good known.remaining
    obtain ⟨buffersP,snapshotP⟩ := ranges_current getP rangesP
    have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotP
    have rawP : (CompressLoop.preparedStream z l n).next_out = .ref (.blk ob) (oo+oldLog.output.length) := raw
    let flush := if (prepare h slot z l n).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
    have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush;split <;>simp
    have newInput : flush = Z_NO_FLUSH → (CompressLoop.preparedStream z l n).avail_in ≠ 0 := by
      intro noFlush
      apply prepare_no_flush_input h slot z l n
      intro zero
      have finish : flush = Z_FINISH := by simp [flush,zero]
      exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (noFlush.symm.trans finish)
    obtain ⟨protocolZ,protocolD,protocolBoundary,protocol,_buffer⟩ :=
      prefix_buffer_protocol history initial.protocol globals ranges pointer notFinished previous
    have sameZ : protocolZ = z := Option.some.inj (protocolBoundary.good.live.hz.symm.trans known.get)
    have sameD : protocolD = d := Option.some.inj (protocolBoundary.good.live.hs.symm.trans counted.protocol.good.live.hs)
    subst protocolZ protocolD
    have finishedInput : d.status = FINISH_STATE → flush = Z_FINISH ∧ (CompressLoop.preparedStream z l n).avail_in = 0 := by
      intro finished
      obtain ⟨zeroPending,zeroInput⟩ := protocol finished
      dsimp only at zeroPending
      subst n
      refine ⟨?_,?_⟩
      · simp only [flush,prepare_empty_input,show ((0 : UInt64) != 0) = false from rfl,Bool.false_eq_true,ite_false]
      · simp only [CompressLoop.preparedStream,zeroInput,beq_self_eq_true,ite_true]
        decide +kernel
    have firstRoom : d.status = INIT_STATE → 2 ≤ (CompressLoop.preparedStream z l n).avail_out.toNat := by
      intro status
      by_cases positiveK : 0 < k
      · rcases oldStatus positiveK with busy | finished
        · exact False.elim ((by decide : BUSY_STATE ≠ INIT_STATE) (busy.symm.trans status))
        · exact False.elim ((by decide : FINISH_STATE ≠ INIT_STATE) (finished.symm.trans status))
      · have zeroK : k = 0 := by omega
        subst k
        obtain ⟨sameHeap,sameLocals⟩ := zero_execution previous
        have sameLocals' := Prod.mk.inj sameLocals
        have leftEq : l = capacity := congrArg Prod.fst sameLocals'.2
        have sameFirst : z = first := Option.some.inj (known.get.symm.trans (by rw [sameHeap];exact initial.protocol.good.live.hz))
        rw [sameFirst,leftEq]
        simp only [CompressLoop.preparedStream,outZero,beq_self_eq_true,ite_true,CompressChunks.chunk_value]
        apply Nat.le_min.mpr
        have formula := ZlibF.Math.DeflateBound.compress_bound_object_formula source.length object
        exact ⟨by omega,by decide⟩
    obtain ⟨read,amount,code,computed,ze,de,run,countedA,_buffersA,accountA,allowed,statusA⟩ :=
      countedP.utility_request flush buffersP rawP positive valid flag newInput firstRoom finishedInput
    obtain ⟨leftEq,pendingEq,engineRun⟩ := engine_of_body known.get actual
    have events := Prod.mk.inj (Except.ok.inj (run.symm.trans engineRun))
    have codeEq := events.1
    have heaps := events.2
    subst computed
    obtain ⟨used,log,za,sound⟩ := actual_prefix_sound history initial.protocol.good.live.hz ranges pointer (ActualPrefix.step previous guard actual)
    have sameZ : ze = za := Option.some.inj (countedA.protocol.good.live.hz.symm.trans sound.get)
    subst ze
    have inPrepare := (prepare_counts h slot z l n).2
    have outPrepare := (prepare_counts h slot z l n).1
    have oldIn := known.inputCount
    have nextIn := sound.inputCount
    have oldOut := known.outputCount
    have nextOut := sound.outputCount
    have inCall := accountA.2.2.1
    have outCall := accountA.2.2.2.1
    dsimp only at oldIn nextIn oldOut nextOut
    change (prepare h slot z l n).2.1.toNat + (CompressLoop.preparedStream z l n).avail_in.toNat = _ at inPrepare
    change (prepare h slot z l n).1.toNat + (CompressLoop.preparedStream z l n).avail_out.toNat = _ at outPrepare
    rw [leftEq] at outPrepare
    rw [pendingEq] at inPrepare
    have usedEq : already + read = used := by omega
    have writtenEq : oldLog.output.length + amount = log.output.length := by omega
    rw [usedEq,writtenEq] at countedA
    refine ⟨used,log,za,de,sound,countedA,?_,fun _ => statusA⟩
    rwa [codeEq] at allowed

private theorem empty_encoding_status {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) : d.status = INIT_STATE := by
  rcases state.phase with ⟨_,_,_input,start,_⟩ | ⟨_,impossible,_⟩ |
    ⟨_,_,_,_,_published,impossible,_⟩ | ⟨_published,impossible,_⟩
  · exact start.status
  · cases impossible
  · cases impossible
  · cases impossible

/-- The actual initializer and actual four binding assignments establish
the counted seed on the real ready heap. No metadata is supplied by the
caller; initialization's own checked producer is used. -/
theorem successful_counted_seed {h initialized ready : Heap} {dest source : BPtr} {first : ZStream}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized))
    (setup : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized = .ok ((),ready))
    (get : ready.streams h.nextBlk = some first)
    (history : DefaultDataTrace (.tab h.nextBlk) ready {}) :
    ∃ d config, CountedBoundary ready (.tab h.nextBlk) (localHeap h).nextBlk first d config 0 0 ∧
      d.status ≠ FINISH_STATE := by
  have domain := automatic_stream_domain h fresh unique globals
  obtain ⟨f,u,g,v,old,getOld,alloc,_null⟩ := domain
  obtain ⟨zi,di,countedI⟩ := observed_default_init_counted_state f u g getOld alloc v actualInit
  let bound := bindings zi dest source
  have getI : initialized.streams h.nextBlk = some zi := countedI.protocol.good.live.hz
  have computedSetup : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized =
      .ok ((),(ZStreamRef.tab h.nextBlk).put initialized bound) := by
    simp [C.run,zwr,ldZStream,stZStream,ZStreamRef.get,ZStreamRef.isRo,getI,bound]
  have readyEq : ready = (ZStreamRef.tab h.nextBlk).put initialized bound :=
    (Prod.mk.inj (Except.ok.inj (setup.symm.trans computedSetup))).2
  have globalsI := ZlibF.Spec.Public.Proofs.DeflateCore.initialized_globals (automatic_stream_domain h fresh unique globals) actualInit
  have edit : Rebuffer initialized ready (.tab h.nextBlk) := by
    rw [readyEq]
    exact buffer_fields_rebuffer countedI.protocol.good globalsI bound rfl
  obtain ⟨za,getA,countedA⟩ := countedI.rebuffer edit
  have sameZ : za = first := Option.some.inj (getA.symm.trans get)
  subst za
  obtain ⟨encodingDs,encodingZ,encodingD,encodingConfig,encoding,_valid⟩ := history.encoding
  have sameZ : encodingZ = first := Option.some.inj (encoding.protocol.good.live.hz.symm.trans get)
  subst encodingZ
  have sameDs : encodingDs = (localHeap h).nextBlk := StateRef.deflate.inj
    (Option.some.inj (encoding.protocol.good.live.zst.symm.trans countedA.protocol.good.live.zst))
  subst encodingDs
  have sameD : encodingD = di := Option.some.inj (encoding.protocol.good.live.hs.symm.trans countedA.protocol.good.live.hs)
  subst encodingD
  exact ⟨di,engineConfig di,countedA,by rw [empty_encoding_status encoding];decide⟩

/-- With adequate advertised capacity, the real large-source wrapper
reaches END and completes its original tail. Its cumulative actual output
is strictly below Bound, so no exhausted-output acknowledgement call is
being silently assumed to succeed. -/
theorem sufficient_large_capacity {h initialized : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (large : 33554432 ≤ xs.length) (room : Api.compressBound xs.length ≤ capacity.toNat)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized)) :
    ∃ output after,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h =
        .ok ((Z_OK,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      output.length < Api.compressBound xs.length := by
  obtain ⟨ready,last,loopHeap,setup,actualLoop,stopped,_valid⟩ :=
    original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
  obtain ⟨ready0,first,setup0,history,get,ranges,out,_in,outAvail,_inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have sameReady := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
  subst ready0
  obtain ⟨d,config,counted,notFinished⟩ := successful_counted_seed fresh unique globals actualInit setup get history
  have setupFrame := setup_frame fresh unique globals actualInit setup
  have globalsReady : LibraryGlobals ready := setupFrame.1.symm.trans globals
  have raw := out.trans pointer
  obtain ⟨scope,length⟩ := ZlibF.Spec.Public.Proofs.CompressBound.source_bytes_object_bound objects bytes
  have object : xs.length < 2^63 := by omega
  obtain ⟨k,_positive,_fuel,execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
  obtain ⟨used,log,returned,result,sound,countedA,allowed,_status⟩ :=
    large_prefix_counted history counted globalsReady ranges raw outAvail notFinished object large room execution
  have ended : last.1 = Z_STREAM_END := allowed.resolve_left stopped
  have budget := countedA.written_compress_bound_strict sound.usedBound object large
  obtain ⟨buffers,_snapshot⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
  have cursor : returned.next_out = .ref (.blk ob) (oo+log.output.length) := by rw [sound.outputPtr,raw];rfl
  have physical : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by rw [←raw];exact sound.outputBytes
  have fits : log.output.length ≤ capacity.toNat := by have count := sound.outputCount;rw [outAvail] at count;simp only [UInt32.toNat_zero,Nat.zero_add] at count;omega
  have capacityScope : capacity.toNat < 2^63 := by
    rcases writable with ⟨impossible,_⟩ | ⟨ref,offset,array,_eq,getA,_ro,bound⟩
    · rw [pointer] at impossible;cases impossible
    · have size := objects ref array getA;change array.size < 2^63 at size;omega
  obtain ⟨ds,da,after,_good,tailRun,finalBytes,_dead,_live,_frame,_count,_next,word⟩ :=
    tail_nonnull_exact sound.history sound.get buffers cursor physical (by omega) last.1
  rw [ended] at tailRun
  simp only [beq_self_eq_true,ite_true] at tailRun
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have whole := run_of_successful_stages fresh bytes nonnull actualInit setup actualLoop
    (by rw [pointer,ended];exact tailRun)
  exact ⟨log.output,after,whole,word,by rw [pointer];exact finalBytes,budget⟩

end ZlibF.Spec.Public.Proofs.CompressLarge
