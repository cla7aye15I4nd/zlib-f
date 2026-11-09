import ZlibF.Proof.«compress.c.finish-input»

/-! # Exact buffer exhaustion and full-source prefix completion -/
namespace ZlibF.Spec.Public.Proofs.CompressBuffer
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressLoop
open ZlibF.Spec.Public.Proofs.CompressPrefix ZlibF.Spec.Public.Proofs.CompressTail
open ZlibF.Spec.Public.Proofs.CompressMemory ZlibF.Spec.Public.Proofs.CompressModes
open ZlibF.Spec.Public.Proofs.CompressFinishInput ZlibF.Spec.Public.Proofs.CompressCompletion
set_option autoImplicit false
set_option maxRecDepth 100000

/-- An actual body result determines its actual engine call and both
refilled local budgets, without any callee property assumption. -/
theorem engine_of_body {h after : Heap} {slot : Nat} {z : ZStream} {old : Int32} {left pending : UInt64} {last : Locals}
    (get : h.streams slot = some z)
    (actual : body (some (.tab slot)) (old,left,pending) h = .ok (last,after)) :
    (prepare h slot z left pending).1 = last.2.1 ∧
    (prepare h slot z left pending).2.1 = last.2.2 ∧
    deflate (some (.tab slot))
      (if (prepare h slot z left pending).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare h slot z left pending).2.2 = .ok (last.1,after) := by
  rw [body_prepare h slot z old left pending get] at actual
  rcases eq : prepare h slot z left pending with ⟨l,n,hp⟩
  simp only [eq,bind_app] at actual ⊢
  cases run : deflate (some (.tab slot)) (if n != 0 then Z_NO_FLUSH else Z_FINISH) hp with
  | error fault => simp only [run] at actual;cases actual
  | ok pair =>
    obtain ⟨rc,tested⟩ := pair
    simp only [run,pure_app] at actual
    obtain ⟨states,heaps⟩ := Prod.mk.inj (Except.ok.inj actual)
    subst last after
    exact ⟨rfl,rfl,rfl⟩

private theorem prepare_zero_pending (h : Heap) (slot : Nat) (z : ZStream) (left : UInt64) :
    (prepare h slot z left 0).2.1 = 0 := by
  have zero : CompressChunks.chunk (0 : UInt64) = 0 := by decide +kernel
  simp only [prepare,zero,show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl]
  split <;>rfl

/-- The real body preserves FINISH_STATE => no offered or unoffered input.
A BUF_ERROR can therefore occur only with zero output budget, and leaves
both the pending output budget and returned avail_out equal to zero. -/
theorem body_buffer_protocol {h after : Heap} {slot ds ob oo : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {old : Int32} {left pending : UInt64} {source : List UInt8} {last : Locals}
    (boundary : DefaultFinishBoundary h (.tab slot) ds z d config) (globals : LibraryGlobals h)
    (ranges : Ranges h (.tab slot) z left pending source) (pointer : z.next_out = .ref (.blk ob) oo)
    (protocol : d.status = FINISH_STATE → pending = 0 ∧ z.avail_in = 0)
    (actual : body (some (.tab slot)) (old,left,pending) h = .ok (last,after)) :
    ∃ za da, DefaultFinishBoundary after (.tab slot) ds za da config ∧
      (da.status = FINISH_STATE → last.2.2 = 0 ∧ za.avail_in = 0) ∧
      (last.1 = Z_BUF_ERROR → last.2.1 = 0 ∧ za.avail_out = 0) := by
  obtain ⟨za,da,boundaryA,_allowed,noFuture⟩ := body_modes boundary globals ranges pointer (fun status => (protocol status).1) actual
  have get : h.streams slot = some z := boundary.good.live.hz
  have edit := prepare_rebuffer boundary.good globals left pending
  obtain ⟨zp,getP,boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left pending :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left pending get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP,snapshotP⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left pending).next_out = .ref (.blk ob) oo := pointer
  obtain ⟨leftEq,pendingEq,engineRun⟩ := engine_of_body get actual
  let flush := if (prepare h slot z left pending).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush;split <;>simp
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotP
  have nonempty : flush = Z_NO_FLUSH → (CompressLoop.preparedStream z left pending).avail_in ≠ 0 := by
    intro noFlush
    apply prepare_no_flush_input h slot z left pending
    intro zero
    have finish : flush = Z_FINISH := by simp [flush,zero]
    exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (noFlush.symm.trans finish)
  have finishFlag : d.status = FINISH_STATE → flush = Z_FINISH := by
    intro status
    have zero := (protocol status).1
    subst pending
    simp only [flush,prepare_zero_pending,show ((0 : UInt64) != 0) = false from rfl,Bool.false_eq_true,ite_false]
  have accepted : d.status = FINISH_STATE → (CompressLoop.preparedStream z left pending).avail_in = 0 := by
    intro status
    obtain ⟨zeroPending,zeroInput⟩ := protocol status
    simp only [CompressLoop.preparedStream,zeroPending,zeroInput,beq_self_eq_true,ite_true]
    decide +kernel
  have emptyA := ordinary_run_finish_input boundaryP buffersP pointerP valid flag nonempty finishFlag accepted
    engineRun boundaryA.good.live.hz boundaryA.good.live.hs
  refine ⟨za,da,boundaryA,fun status => ⟨noFuture status,emptyA status⟩,?_⟩
  intro buf
  have empty : (CompressLoop.preparedStream z left pending).avail_out = 0 := by
    apply Classical.byContradiction
    intro nonzero
    have positive : 0 < (CompressLoop.preparedStream z left pending).avail_out.toNat := by
      have nz : (CompressLoop.preparedStream z left pending).avail_out.toNat ≠ 0 := fun e => nonzero (UInt32.toNat_inj.mp e)
      omega
    rcases flag with noFlush | finish
    · have unfinished : d.status ≠ FINISH_STATE := by intro done;exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (noFlush.symm.trans (finishFlag done))
      obtain ⟨used,produced,tested,ze,de,run,_boundary,_buffers,_account,_busy⟩ :=
        boundaryP.no_flush buffersP pointerP positive valid (nonempty noFlush) unfinished
      have actualNF := engineRun
      change deflate (some (.tab slot)) flush _ = _ at actualNF
      rw [noFlush] at actualNF
      have code := (Prod.mk.inj (Except.ok.inj (run.symm.trans actualNF))).1
      exact (by decide : Z_OK ≠ Z_BUF_ERROR) (code.trans buf)
    · obtain ⟨used,produced,code,tested,ze,de,run,_boundary,_buffers,_account,allowed,_ended⟩ :=
        boundaryP.finish buffersP pointerP positive valid accepted
      have actualF := engineRun
      change deflate (some (.tab slot)) flush _ = _ at actualF
      rw [finish] at actualF
      have same := (Prod.mk.inj (Except.ok.inj (run.symm.trans actualF))).1
      rcases allowed with ok | done
      · exact (by decide : Z_OK ≠ Z_BUF_ERROR) (ok.symm.trans (same.trans buf))
      · exact (by decide : Z_STREAM_END ≠ Z_BUF_ERROR) (done.symm.trans (same.trans buf))
  have zeroBudget : z.avail_out.toNat + left.toNat = 0 := by
    have notPositive : ¬0 < left.toNat+z.avail_out.toNat := by
      intro room
      have positive := prepare_output_positive z left pending room
      rw [empty] at positive
      cases positive
    omega
  have counts := (prepare_counts h slot z left pending).1
  change (prepare h slot z left pending).1.toNat + (CompressLoop.preparedStream z left pending).avail_out.toNat = _ at counts
  have leftZero : last.2.1 = 0 := UInt64.toNat_inj.mp (by rw [←leftEq];rw [empty] at counts;change _=0;omega)
  have sourceRefusal := public_zero_output_refusal boundaryP.good flush
    (by rcases flag with eq|eq <;>rw [eq] <;>decide) (by rcases flag with eq|eq <;>rw [eq] <;>decide)
    (by rw [pointerP];intro bad;cases bad) valid finishFlag empty
  obtain ⟨message,refusal,refused,_buffers,_account⟩ := public_entry_refusal_protocol flush Z_BUF_ERROR boundaryP buffersP sourceRefusal
  have heaps := (Prod.mk.inj (Except.ok.inj (refusal.symm.trans engineRun))).2
  have getRefused := refused.good.live.hz
  rw [heaps] at getRefused
  have same : {CompressLoop.preparedStream z left pending with msg := message} = za :=
    Option.some.inj (getRefused.symm.trans boundaryA.good.live.hz)
  exact ⟨leftZero,by rw [←same];exact empty⟩

/-- Every finite real wrapper prefix establishes the strong finish-input
protocol. On BUF_ERROR both remaining output counters are zero. -/
theorem prefix_buffer_protocol {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {d : DeflateState} {config : EngineConfig}
    {capacity pending : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : DefaultFinishBoundary start (.tab slot) ds first d config)
    (globals : LibraryGlobals start) (ranges : Ranges start (.tab slot) first capacity pending source)
    (pointer : first.next_out = .ref (.blk ob) oo) (initialStatus : d.status ≠ FINISH_STATE)
    (execution : ActualPrefix slot start (Z_OK,capacity,pending) k after last) :
    ∃ za da, DefaultFinishBoundary after (.tab slot) ds za da config ∧
      (da.status = FINISH_STATE → last.2.2 = 0 ∧ za.avail_in = 0) ∧
      (last.1 = Z_BUF_ERROR → last.2.1 = 0 ∧ za.avail_out = 0) := by
  induction execution with
  | nil =>
    exact ⟨first,d,initial,fun status => False.elim (initialStatus status),fun buf => False.elim ((by decide : Z_OK ≠ Z_BUF_ERROR) buf)⟩
  | @step k h after current next previous _guard actual ih =>
    obtain ⟨za,da,boundary,protocol,_oldBuf⟩ := ih
    obtain ⟨used,log,observed,sound⟩ := actual_prefix_sound history initial.good.live.hz ranges pointer previous
    have same : za = observed := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
    subst za
    have frame := prefix_frame history initial ranges pointer previous
    have currentGlobals : LibraryGlobals h := frame.1.symm.trans globals
    have raw : observed.next_out = .ref (.blk ob) (oo+log.output.length) := by rw [sound.outputPtr,pointer];rfl
    rcases current with ⟨old,l,n⟩
    exact body_buffer_protocol boundary currentGlobals sound.remaining raw protocol actual

/-- All actually emitted wrapper prefixes extend to an independently valid
stream for the entire original source. The strong actual finish-input
protocol closes the final-block case; nonfinal phases append literal data,
including every not-yet-offered source byte. BUF_ERROR exactly fills cap. -/
theorem prefix_buffer_result {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {d : DeflateState} {config : EngineConfig}
    {capacity pending : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : DefaultFinishBoundary start (.tab slot) ds first d config)
    (globals : LibraryGlobals start) (ranges : Ranges start (.tab slot) first capacity pending source)
    (pointer : first.next_out = .ref (.blk ob) oo) (initialStatus : d.status ≠ FINISH_STATE)
    (outAvail : first.avail_out = 0)
    (execution : ActualPrefix slot start (Z_OK,capacity,pending) k after last) :
    ∃ used log za, PrefixAccount slot first capacity pending source k after last used log za ∧
      (last.1 = Z_BUF_ERROR → log.output.length = capacity.toNat) ∧
      ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete source ∧ log.output <+: complete := by
  obtain ⟨used,log,za,sound⟩ := actual_prefix_sound history initial.good.live.hz ranges pointer execution
  obtain ⟨current,dCurrent,boundary,protocol,buffer⟩ := prefix_buffer_protocol history initial globals ranges pointer initialStatus execution
  have sameZ : current = za := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
  subst current
  obtain ⟨encodingDs,encodingZ,encodingD,encodingConfig,encoding,_valid⟩ := sound.history.encoding
  have sameEncodingZ : encodingZ = za := Option.some.inj (encoding.protocol.good.live.hz.symm.trans sound.get)
  subst encodingZ
  have sameDs : encodingDs = ds := StateRef.deflate.inj (Option.some.inj (encoding.protocol.good.live.zst.symm.trans boundary.good.live.zst))
  subst encodingDs
  have sameD : encodingD = dCurrent := Option.some.inj (encoding.protocol.good.live.hs.symm.trans boundary.good.live.hs)
  subst encodingD
  have content : log.input <+: source := by rw [sound.input];exact ⟨source.drop used,List.take_append_drop _ _⟩
  have finished : dCurrent.status = FINISH_STATE → log.input = source := by
    intro status
    obtain ⟨pendingZero,inputZero⟩ := protocol status
    have counts := sound.inputCount
    rw [pendingZero,inputZero] at counts
    simp only [UInt32.toNat_zero,UInt64.toNat_zero,Nat.zero_add] at counts
    have totalSize := caller_bytes_length ranges.snapshot
    have all : used = source.length := by omega
    rw [sound.input,all,List.take_length]
  refine ⟨used,log,za,sound,?_,encoding_target_completion encoding content finished⟩
  intro buf
  obtain ⟨leftZero,outZero⟩ := buffer buf
  have count := sound.outputCount
  rw [leftZero,outZero,outAvail] at count
  simpa only [UInt32.toNat_zero,UInt64.toNat_zero,Nat.zero_add] using count

private theorem initial_encoding_status {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) : d.status = INIT_STATE := by
  rcases state.phase with ⟨_,_,_input,start,_⟩ | ⟨_,impossible,_⟩ |
    ⟨_,_,_,_,_published,impossible,_⟩ | ⟨_published,impossible,_⟩
  · exact start.status
  · cases impossible
  · cases impossible
  · cases impossible

/-- The same real BUF_ERROR return, including pointer difference and
cleanup, exactly fills the original capacity. Its final physical output
extends to a valid stream for the complete original source. -/
theorem initialized_buffer_result {h initialized after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n written : UInt64} {xs output : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized))
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((Z_BUF_ERROR,some written),after))
    (physical : Bytes after dest written.toNat output) :
    output.length = capacity.toNat ∧
      ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete xs ∧ output <+: complete := by
  obtain ⟨ready,last,loopHeap,setup,actualLoop,_stopped,_valid⟩ :=
    original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
  obtain ⟨ready0,first,setup0,history,get,ranges,out,_in,outAvail,_inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have sameReady := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
  subst ready0
  obtain ⟨ds,z,d,config,encoding,_valid⟩ := history.encoding
  have firstEq : z = first := Option.some.inj (encoding.protocol.good.live.hz.symm.trans get)
  subst z
  have initialStatus : d.status ≠ FINISH_STATE := by rw [initial_encoding_status encoding];decide
  have setupFrame := setup_frame fresh unique globals actualInit setup
  have globalsReady : LibraryGlobals ready := setupFrame.1.symm.trans globals
  have raw := out.trans pointer
  obtain ⟨k,_positive,_fuel,execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
  obtain ⟨used,log,returned,sound,buffer,complete,completeValid,extension⟩ :=
    prefix_buffer_result history encoding.protocol globalsReady ranges raw initialStatus outAvail execution
  obtain ⟨buffers,_input⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
  have cursor : returned.next_out = .ref (.blk ob) (oo+log.output.length) := by rw [sound.outputPtr,raw];rfl
  have outputBytes : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by rw [←raw];exact sound.outputBytes
  have fits : log.output.length ≤ capacity.toNat := by
    have count := sound.outputCount
    rw [outAvail] at count
    simp only [UInt32.toNat_zero,Nat.zero_add] at count
    omega
  have capacityBound : capacity.toNat < 2^63 := by
    rcases writable with ⟨impossible,_⟩ | ⟨ref,offset,a,_eq,getA,_ro,bound⟩
    · rw [pointer] at impossible
      cases impossible
    · have size := objects ref a getA
      change a.size < 2^63 at size
      omega
  obtain ⟨tailDs,tailD,tested,_good,tailRun,finalBytes,_dead,_live,_frame,_count,_next,wordNat⟩ :=
    tail_nonnull_exact sound.history sound.get buffers cursor outputBytes (by omega) last.1
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have computedRun := run_of_successful_stages fresh bytes nonnull actualInit setup actualLoop (by rw [pointer];exact tailRun)
  have events := Prod.mk.inj (Except.ok.inj (computedRun.symm.trans actual))
  have code := congrArg Prod.fst events.1
  have scalar := Option.some.inj (congrArg Prod.snd events.1)
  have heapEq := events.2
  have bufferCode : last.1 = Z_BUF_ERROR := by
    by_cases ended : last.1 = Z_STREAM_END
    · have impossible : Z_OK = Z_BUF_ERROR := by simpa only [ended,beq_self_eq_true,ite_true] using code
      cases (by decide : Z_OK ≠ Z_BUF_ERROR) impossible
    · simpa only [beq_iff_eq,ended,ite_false] using code
  have usedAllRoom := buffer bufferCode
  have exactLength : written.toNat = log.output.length := by rw [←scalar];exact wordNat
  have physicalLog : Bytes after dest written.toNat log.output := by
    rw [exactLength,pointer,←heapEq]
    exact finalBytes
  have sameOutput := observed_bytes_unique physicalLog physical
  rw [sameOutput] at usedAllRoom extension
  exact ⟨usedAllRoom,complete,completeValid,extension⟩

/-- BUF_ERROR's exact-capacity and full-source format-prefix conclusion
holds for every actual return in the internal raw domain and every oracle. -/
theorem actual_buffer_result {h after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n written : UInt64} {xs output : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((Z_BUF_ERROR,some written),after))
    (physical : Bytes after dest written.toNat output) :
    output.length = capacity.toNat ∧
      ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete xs ∧ output <+: complete := by
  obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨initRc,initialized,actualInit,allowed⟩ := default_initialization_total f u g get alloc v
  rcases allowed with ok | memory
  · subst initRc
    exact initialized_buffer_result fresh unique globals objects bytes writable separate pointer actualInit actual physical
  · subst initRc
    have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
    obtain ⟨code,_scalar,_failed⟩ := memory_return_effects fresh unique globals bytes nonnull actualInit actual
    exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) code)

/-- Default raw utilities have complete return-mode semantics, exact
physical writeback and caller memory effects. BUF_ERROR fills the capacity
and is a prefix of a valid encoding of the full original source. The
remaining independent clauses are output-size <= compressBound and
BUF_ERROR capacity < compressBound; neither is assumed here. -/
theorem default_wrapper_buffer_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧
      (rc = Z_MEM_ERROR → output = [] ∧ AllocationFailed h after) ∧
      (rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs) ∧
      (rc = Z_BUF_ERROR → output.length = capacity.toNat ∧
        ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete xs ∧ output <+: complete) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,length,fits,physical,store,frame,allowed,memory,valid,live,dead⟩ :=
    default_wrapper_modes_total fresh unique globals objects bytes writable separate pointer
  refine ⟨rc,output,after,expected,actual,length,fits,physical,store,frame,allowed,memory,valid,?_,live,dead⟩
  intro buf
  subst rc
  exact actual_buffer_result fresh unique globals objects bytes writable separate pointer actual (by rw [length];exact physical)

/-- All four real default entries share the exact same data, scalar,
frame and non-OK semantics. The independent Bound clauses stay separate. -/
theorem default_buffer_family_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress_z dest (some capacity) source n) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress2 dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      C.run (compress dest (some capacity) source n) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧
      (rc = Z_MEM_ERROR → output = [] ∧ AllocationFailed h after) ∧
      (rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs) ∧
      (rc = Z_BUF_ERROR → output.length = capacity.toNat ∧
        ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete xs ∧ output <+: complete) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,length,fits,physical,store,frame,allowed,memory,valid,buffer,live,dead⟩ :=
    default_wrapper_buffer_total fresh unique globals objects bytes writable separate pointer
  have compat := compatibility_run_of_z actual
  exact ⟨rc,output,after,expected,actual,actual,compat,compat,length,fits,physical,store,frame,allowed,memory,valid,buffer,live,dead⟩

end ZlibF.Spec.Public.Proofs.CompressBuffer
