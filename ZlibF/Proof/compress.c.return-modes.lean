import ZlibF.Proof.«compress.c.zero-capacity»
import ZlibF.Proof.«deflate.c.engine.no-flush-protocol»

/-! # Actual default wrapper return modes before bound-based completion -/
namespace ZlibF.Spec.Public.Proofs.CompressModes
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressLoop
open ZlibF.Spec.Public.Proofs.CompressPrefix ZlibF.Spec.Public.Proofs.CompressTail
open ZlibF.Spec.Public.Proofs.CompressMemory ZlibF.Spec.Public.Proofs.CompressZero
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem no_pending_after_prepare (h : Heap) (slot : Nat) (z : ZStream) (left : UInt64) :
    (prepare h slot z left 0).2.1 = 0 := by
  have zero : CompressChunks.chunk (0 : UInt64) = 0 := by decide +kernel
  simp only [prepare,zero,show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl]
  split <;> rfl

private theorem trace_calls {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : DeflateCore.Calls r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw observed ih =>
    obtain ⟨z,_z',getZ,_getA,buffers,_active,_snapshot,_used,_written,run⟩ := observed
    have same : z = _ := Option.some.inj (getZ.symm.trans get)
    subst z
    exact .step ih get buffers raw run

/-- The real wrapper cannot choose NO_FLUSH after its state starts
finishing: no still-unoffered input remains then. Hence every actual body
returns OK, END or BUF_ERROR, never STREAM_ERROR. The invariant concerns
unoffered source only; it does not claim finite completion of that source. -/
theorem body_modes {h after : Heap} {slot ds ob oo : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {old : Int32} {left pending : UInt64} {source : List UInt8} {last : Locals}
    (boundary : DefaultFinishBoundary h (.tab slot) ds z d config) (globals : LibraryGlobals h)
    (ranges : Ranges h (.tab slot) z left pending source) (pointer : z.next_out = .ref (.blk ob) oo)
    (protocol : d.status = FINISH_STATE → pending = 0)
    (actual : body (some (.tab slot)) (old,left,pending) h = .ok (last,after)) :
    ∃ za da, DefaultFinishBoundary after (.tab slot) ds za da config ∧
      (last.1 = Z_OK ∨ last.1 = Z_STREAM_END ∨ last.1 = Z_BUF_ERROR) ∧
      (da.status = FINISH_STATE → last.2.2 = 0) := by
  have get : h.streams slot = some z := boundary.good.live.hz
  have edit := prepare_rebuffer boundary.good globals left pending
  obtain ⟨zp,getP,boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left pending :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left pending get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP,snapshotP⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left pending).next_out = .ref (.blk ob) oo := pointer
  let flush := if (prepare h slot z left pending).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush;split <;>simp
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotP
  have endFlag : d.status = FINISH_STATE → flush = Z_FINISH := by
    intro status
    have zero := protocol status
    subst pending
    simp only [flush,no_pending_after_prepare,show ((0 : UInt64) != 0) = false from rfl,Bool.false_eq_true,ite_false]
  obtain ⟨used,written,rc,computed,za,da,engineRun,boundaryA,_buffersA,_goodA,account,
    _bytes,_tin,_tout,allowed,errors,_bad,_ended,_shape,_frame,_live,_count,_next⟩ :=
    boundaryP.all_scalar_request_contract flush buffersP (Or.inr ⟨ob,oo,pointerP⟩)
  have bodyRun : body (some (.tab slot)) (old,left,pending) h =
      .ok ((rc,(prepare h slot z left pending).1,(prepare h slot z left pending).2.1),computed) := by
    rw [body_prepare h slot z old left pending get]
    change deflate (some (.tab slot))
      (if (prepare h slot z left pending).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare h slot z left pending).2.2 = .ok (rc,computed) at engineRun
    rcases eq : prepare h slot z left pending with ⟨l,n,hp⟩
    simp only [eq] at engineRun ⊢
    simp only [bind_app,engineRun,pure_app]
  obtain ⟨states,heaps⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
  subst computed last
  have noStream : rc ≠ Z_STREAM_ERROR := by
    intro error
    have cases := errors.mp error
    rcases cases with lo | hi | null | ⟨null,nonzero⟩ | ⟨status,wrong⟩
    · rcases flag with eq | eq <;>rw [eq] at lo <;>cases lo
    · rcases flag with eq | eq <;>rw [eq] at hi <;>cases hi
    · rw [pointerP] at null
      cases null
    · exact valid nonzero null
    · exact wrong (endFlag status)
  refine ⟨za,da,boundaryA,?_,?_⟩
  · rcases allowed with ok | done | bad | buf
    · exact Or.inl ok
    · exact Or.inr (Or.inl done)
    · exact False.elim (noStream bad)
    · exact Or.inr (Or.inr buf)
  · intro statusA
    by_cases noPending : (prepare h slot z left pending).2.1 = 0
    · exact noPending
    · have noFlush : flush = Z_NO_FLUSH := by simp [flush,noPending]
      have unfinished : d.status ≠ FINISH_STATE := by
        intro finished
        exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (noFlush.symm.trans (endFlag finished))
      by_cases empty : (CompressLoop.preparedStream z left pending).avail_out = 0
      · have sourceRefusal := public_zero_output_refusal boundaryP.good flush
          (by rw [noFlush];decide) (by rw [noFlush];decide)
          (by rw [pointerP];intro bad;cases bad) valid endFlag empty
        obtain ⟨message,refusal,refused,_buffers,_account⟩ :=
          public_entry_refusal_protocol flush Z_BUF_ERROR boundaryP buffersP sourceRefusal
        have heaps := (Prod.mk.inj (Except.ok.inj (refusal.symm.trans engineRun))).2
        have hs := refused.good.live.hs
        rw [heaps] at hs
        have same : d = da := Option.some.inj (hs.symm.trans boundaryA.good.live.hs)
        exact False.elim (unfinished ((congrArg DeflateState.status same).trans statusA))
      · have positive : 0 < (CompressLoop.preparedStream z left pending).avail_out.toNat := by
          have nonzero : (CompressLoop.preparedStream z left pending).avail_out.toNat ≠ 0 := fun e => empty (UInt32.toNat_inj.mp e)
          omega
        have offered := prepare_no_flush_input h slot z left pending noPending
        obtain ⟨accepted,produced,final,ze,de,run,stateE,_buffersE,_accountE,busy⟩ :=
          boundaryP.no_flush buffersP pointerP positive valid offered unfinished
        rw [noFlush] at engineRun
        have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans engineRun))).2
        have hs := stateE.good.live.hs
        rw [heaps] at hs
        have same : de = da := Option.some.inj (hs.symm.trans boundaryA.good.live.hs)
        rw [same,statusA] at busy
        cases (by decide : FINISH_STATE ≠ BUSY_STATE) busy

/-- Every finite real wrapper prefix retains its no-unoffered-input-after-
FINISH protocol and admits only the three ordinary engine return modes. -/
theorem prefix_modes {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {d : DeflateState} {config : EngineConfig}
    {left pending : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : DefaultFinishBoundary start (.tab slot) ds first d config)
    (ranges : Ranges start (.tab slot) first left pending source)
    (pointer : first.next_out = .ref (.blk ob) oo) (initialStatus : d.status ≠ FINISH_STATE)
    (execution : ActualPrefix slot start (Z_OK,left,pending) k after last) :
    ∃ za da, DefaultFinishBoundary after (.tab slot) ds za da config ∧
      (last.1 = Z_OK ∨ last.1 = Z_STREAM_END ∨ last.1 = Z_BUF_ERROR) ∧
      (da.status = FINISH_STATE → last.2.2 = 0) := by
  induction execution with
  | nil => exact ⟨first,d,initial,Or.inl rfl,fun status => False.elim (initialStatus status)⟩
  | @step k h after current next previous _guard actual ih =>
    obtain ⟨za,da,boundary,_allowed,protocol⟩ := ih
    obtain ⟨used,log,observed,sound⟩ := actual_prefix_sound history initial.good.live.hz ranges pointer previous
    have same : za = observed := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
    subst za
    have globals := ZlibF.Spec.Public.Proofs.DeflateCore.calls_globals (trace_calls sound.history)
    have raw : observed.next_out = .ref (.blk ob) (oo+log.output.length) := by
      rw [sound.outputPtr,pointer]
      rfl
    rcases current with ⟨old,l,n⟩
    exact body_modes boundary globals sound.remaining raw protocol actual

private theorem readable_guard {h : Heap} {dest source : BPtr} {capacity n : UInt64} {xs : List UInt8}
    (bytes : Bytes h source n.toNat xs) (nonnull : dest ≠ .null) :
    ((n>0 && source == .null) || (capacity>0 && dest == .null)) = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  have cases : (n>0 ∧ source = .null) ∨ (capacity>0 ∧ dest = .null) := by
    simpa only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using bad
  rcases cases with ⟨positive,null⟩ | ⟨_,null⟩
  · rw [null] at bytes
    rcases bytes with ⟨_,zero,_⟩ | ⟨_,_,_,impossible,_⟩
    · have gt := UInt64.lt_iff_toNat_lt.mp positive
      change 0 < n.toNat at gt
      omega
    · cases impossible
  · exact nonnull null

/-- The actual translated tail's returned code is its exact final C
normalization, regardless of the values returned by End. -/
theorem tail_return_code {h after : Heap} {strm : ZStreamPtr} {dest : BPtr} {err rc : Int32} {stored : Option UInt64}
    (actual : tail strm dest err h = .ok ((rc,stored),after)) :
    rc = if err == Z_STREAM_END then Z_OK else err := by
  simp only [tail,bind_app] at actual
  cases read : zrd strm (·.next_out) h with
  | error fault => simp only [read] at actual;cases actual
  | ok pair =>
    obtain ⟨pointer,h1⟩ := pair
    simp only [read] at actual
    cases difference : ptrDiff pointer dest h1 with
    | error fault => simp only [difference] at actual;cases actual
    | ok pair =>
      obtain ⟨n,h2⟩ := pair
      simp only [difference] at actual
      cases ended : deflateEnd strm h2 with
      | error fault => simp only [ended] at actual;cases actual
      | ok pair =>
        obtain ⟨ignored,h3⟩ := pair
        simp only [ended] at actual
        cases freed : freeZStream strm h3 with
        | error fault => simp only [freed] at actual;cases actual
        | ok pair =>
          obtain ⟨unit,h4⟩ := pair
          simp only [freed,pure_app] at actual
          exact (congrArg Prod.fst (Prod.mk.inj (Except.ok.inj actual)).1).symm

private theorem tail_of_stages {h initialized ready loopHeap after : Heap} {dest source : BPtr}
    {capacity n finalLeft finalPending : UInt64} {xs : List UInt8} {err rc : Int32} {stored : Option UInt64}
    (fresh : Fresh h) (bytes : Bytes h source n.toNat xs) (nonnull : dest ≠ .null)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized))
    (setup : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized = .ok ((),ready))
    (actualLoop : loop (some (.tab h.nextBlk)) (Z_OK,capacity,n) ready = .ok ((err,finalLeft,finalPending),loopHeap))
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,stored),after)) :
    tail (some (.tab h.nextBlk)) dest err loopHeap = .ok ((rc,stored),after) := by
  have guard := readable_guard (capacity := capacity) bytes nonnull
  have automatic : preInit h = .ok ((some (.tab h.nextBlk),.ref (.str 57) 0),localHeap h) := automatic_stream_run h fresh
  change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
  change zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source) initialized = _ at setup
  rw [compress2_z_stages] at actual
  simpa only [C.run,sizeof_z_stream,guard,Bool.false_eq_true,ite_false,bind_app,automatic,actualInit,
    show (Z_OK != Z_OK) = false from rfl,setup,actualLoop] using actual

private theorem empty_encoding_status {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) : d.status = INIT_STATE := by
  rcases state.phase with ⟨_,_,_input,start,_⟩ | ⟨_,impossible,_⟩ |
    ⟨_,_,_,_,_published,impossible,_⟩ | ⟨_published,impossible,_⟩
  · exact start.status
  · cases impossible
  · cases impossible
  · cases impossible

/-- Every actual default raw-output utility return after successful init
is OK or BUF_ERROR. Legal arguments cannot produce STREAM_ERROR and the
data loop performs no further allocation. -/
theorem initialized_return_modes {h initialized after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8} {rc : Int32} {stored : Option UInt64}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized))
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,stored),after)) :
    rc = Z_OK ∨ rc = Z_BUF_ERROR := by
  obtain ⟨ready,last,loopHeap,setup,actualLoop,stopped,_valid⟩ :=
    original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
  obtain ⟨ready0,first,setup0,history,get,ranges,out,_in,_outAvail,_inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have same := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
  subst ready0
  obtain ⟨ds,z,d,config,encoding,_valid⟩ := history.encoding
  have sameZ : z = first := Option.some.inj (encoding.protocol.good.live.hz.symm.trans get)
  subst z
  have initialStatus : d.status ≠ FINISH_STATE := by rw [empty_encoding_status encoding];decide
  have raw := out.trans pointer
  obtain ⟨k,_positive,_fuel,execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
  obtain ⟨za,da,_boundary,allowed,_protocol⟩ := prefix_modes history encoding.protocol ranges raw initialStatus execution
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have tailRun := tail_of_stages fresh bytes nonnull actualInit setup actualLoop actual
  have code := tail_return_code tailRun
  rcases allowed with okay | finished | buffer
  · exact False.elim (stopped okay)
  · exact Or.inl (by simpa only [finished,beq_self_eq_true,ite_true] using code)
  · exact Or.inr (by simpa only [buffer,show (Z_BUF_ERROR == Z_STREAM_END) = false from rfl,Bool.false_eq_true,ite_false] using code)

/-- An actual init MEM_ERROR is the real early wrapper return. The scalar
is zero and some actually consumed allocation index rejected allocation. -/
theorem memory_return_effects {h initialized after : Heap} {dest source : BPtr}
    {capacity n : UInt64} {xs : List UInt8} {rc : Int32} {stored : Option UInt64}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs) (nonnull : dest ≠ .null)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_MEM_ERROR,initialized))
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,stored),after)) :
    rc = Z_MEM_ERROR ∧ stored = some 0 ∧ AllocationFailed h after := by
  obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨_requests,failed⟩ := memory_requests f u g get alloc v actualInit
  have automatic : preInit h = .ok ((some (.tab h.nextBlk),.ref (.str 57) 0),localHeap h) := automatic_stream_run h fresh
  have guard := readable_guard (capacity := capacity) bytes nonnull
  rw [compress2_z_stages] at actual
  change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
  simp only [C.run,sizeof_z_stream,guard,Bool.false_eq_true,ite_false,bind_app,automatic,actualInit,
    show (Z_MEM_ERROR != Z_OK) = true from rfl,ite_true] at actual
  cases live : initialized.streams h.nextBlk with
  | none => simp only [freeZStream,live] at actual;cases actual
  | some z =>
    simp only [freeZStream,live,pure_app] at actual
    have events := Prod.mk.inj (Except.ok.inj actual)
    have code := congrArg Prod.fst events.1
    have scalar := congrArg Prod.snd events.1
    have heapEq := events.2
    refine ⟨code.symm,scalar.symm,?_⟩
    obtain ⟨i,lower,upper,rejected⟩ := failed
    exact ⟨i,lower,by rw [←heapEq];exact upper,rejected⟩

/-- All legal default raw-output utility returns are OK, BUF_ERROR or
MEM_ERROR. A memory error clears the stored length and has an actual
allocation-failure witness, on the exact returned heap. -/
theorem actual_return_modes {h after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8} {rc : Int32} {stored : Option UInt64}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actual : C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,stored),after)) :
    (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧
      (rc = Z_MEM_ERROR → stored = some 0 ∧ AllocationFailed h after) := by
  obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨initRc,initialized,actualInit,allowed⟩ := default_initialization_total f u g get alloc v
  rcases allowed with ok | memory
  · subst initRc
    have modes := initialized_return_modes fresh unique globals objects bytes writable separate pointer actualInit actual
    refine ⟨?_,?_⟩
    · rcases modes with okay | buffer
      · exact Or.inl okay
      · exact Or.inr (Or.inl buffer)
    · intro error
      rcases modes with okay | buffer
      · exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) (okay.symm.trans error))
      · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) (buffer.symm.trans error))
  · subst initRc
    have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
    obtain ⟨code,scalar,failed⟩ := memory_return_effects fresh unique globals bytes nonnull actualInit actual
    exact ⟨Or.inr (Or.inr code),fun _ => ⟨scalar,failed⟩⟩

/-- The actual default utility execution combines precise memory effects
with its exact three return modes. MEM_ERROR means no output and a real
failed allocation index. BUF_ERROR completion for the whole original source
and the separate compressBound clauses are not asserted by this theorem. -/
theorem default_wrapper_modes_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h =
        .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ Store h dest output expected ∧
      Frame expected after (fun _ => False) ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧
      (rc = Z_MEM_ERROR → output = [] ∧ AllocationFailed h after) ∧
      (rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,length,fits,physical,store,frame,valid,live,dead⟩ :=
    default_wrapper_store_total fresh unique globals objects bytes writable separate pointer
  obtain ⟨allowed,memory⟩ := actual_return_modes fresh unique globals objects bytes writable separate pointer actual
  refine ⟨rc,output,after,expected,actual,length,fits,physical,store,frame,allowed,?_,valid,live,dead⟩
  intro error
  obtain ⟨scalar,failed⟩ := memory error
  have zero : UInt64.ofNat output.length = 0 := Option.some.inj scalar
  have zeroNat := congrArg UInt64.toNat zero
  rw [length] at zeroNat
  exact ⟨List.eq_nil_iff_length_eq_zero.mpr zeroNat,failed⟩

end ZlibF.Spec.Public.Proofs.CompressModes
