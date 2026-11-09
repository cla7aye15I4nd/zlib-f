import ZlibF.Proof.«compress.c.buffer-result»
import ZlibF.Proof.«deflate.c.engine.first-finish-compress-bound»

/-! # The small-source branch of the unchanged compressor capacity promise

This branch covers sources shorter than 2^25 with the existing internal
Uniq/raw-output/default configuration. Larger multi-offer sources remain
separate. The actual first FINISH theorem is proved in the frozen size
stack; it is reused directly rather than assumed as a callee contract.
-/
namespace ZlibF.Spec.Public.Proofs.CompressSmall
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Math.DeflateBound
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressLoop
open ZlibF.Spec.Public.Proofs.CompressPrefix ZlibF.Spec.Public.Proofs.CompressTail
open ZlibF.Spec.Public.Proofs.CompressMemory ZlibF.Spec.Public.Proofs.CompressModes
open ZlibF.Spec.Public.Proofs.CompressBuffer
set_option autoImplicit false
set_option maxRecDepth 100000

/-- This entire source and its advertised bound fit one real uInt offer. -/
theorem small_bound_fits {n : Nat} (small : n < 2^25) :
    n ≤ 2^32-1 ∧ Api.compressBound n ≤ 2^32-1 := by
  have scope : n < 2^63 := by omega
  have formula := compress_bound_object_formula n scope
  rw [formula]
  change n ≤ 4294967295 ∧ n+n/4096+n/16384+n/33554432+13 ≤ 4294967295
  change n < 33554432 at small
  omega

private theorem empty_start {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) :
    ∃ input, EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input 0 0 [] config := by
  rcases state.phase with ⟨_,_,input,start,boundary⟩ | ⟨_,impossible,_⟩ |
    ⟨_,_,_,_,_published,impossible,_⟩ | ⟨_published,impossible,_⟩
  · exact ⟨input,start,boundary⟩
  · cases impossible
  · cases impossible
  · cases impossible

/-- With sufficient advertised room, the real small-source wrapper's
first refill offers the whole source and enough uInt output. Its actual
first loop iteration returns END within compressBound, including exact
terminal exhaustion. No subsequent wrapper iteration is taken. -/
theorem first_loop_bound {h : Heap} {slot ob oo : Nat} {first : ZStream}
    {capacity n : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) h {}) (get : h.streams slot = some first)
    (globals : LibraryGlobals h) (ranges : Ranges h (.tab slot) first capacity n source)
    (pointer : first.next_out = .ref (.blk ob) oo) (inAvail : first.avail_in = 0) (outAvail : first.avail_out = 0)
    (small : source.length < 2^25) (room : Api.compressBound source.length ≤ capacity.toNat) :
    ∃ after remaining used log za,
      loop (some (.tab slot)) (Z_OK,capacity,n) h = .ok ((Z_STREAM_END,remaining,0),after) ∧
      PrefixAccount slot first capacity n source 1 after (Z_STREAM_END,remaining,0) used log za ∧
      log.output.length ≤ Api.compressBound source.length := by
  have length := caller_bytes_length ranges.snapshot
  simp only [inAvail,UInt32.toNat_zero,Nat.zero_add] at length
  obtain ⟨inputFit,boundFit⟩ := small_bound_fits small
  have chunkInput : (CompressChunks.chunk n).toNat = n.toNat := by
    rw [CompressChunks.chunk_value,Nat.min_eq_left]
    omega
  have chunkWord : (CompressChunks.chunk n).toUInt64 = n := UInt64.toNat_inj.mp (by
    rw [UInt32.toNat_toUInt64,chunkInput])
  have pendingZero : (prepare h slot first capacity n).2.1 = 0 := by
    simp only [prepare,inAvail,outAvail,beq_self_eq_true,ite_true,chunkWord,UInt64.sub_self]
  obtain ⟨ds,z,d,config,encoding,_valid⟩ := history.encoding
  have same : z = first := Option.some.inj (encoding.protocol.good.live.hz.symm.trans get)
  subst z
  have edit := prepare_rebuffer encoding.protocol.good globals capacity n
  obtain ⟨zp,getP,encodingP⟩ := encoding.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream first capacity n :=
    Option.some.inj (getP.symm.trans (prepare_get h slot first capacity n get))
  subst zp
  obtain ⟨input,start,boundary⟩ := empty_start encodingP
  have rangesP := prepare_ranges encoding.protocol.good ranges
  obtain ⟨buffers,snapshot⟩ := ranges_current getP rangesP
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
  have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans encodingP.protocol.configuration.level
  have pointerP : (CompressLoop.preparedStream first capacity n).next_out = .ref (.blk ob) oo := pointer
  have fullInput : (CompressLoop.preparedStream first capacity n).avail_in.toNat = source.length := by
    simp only [CompressLoop.preparedStream,inAvail,beq_self_eq_true,ite_true,chunkInput]
    exact length.symm
  have outputRoom : Api.compressBound (CompressLoop.preparedStream first capacity n).avail_in.toNat ≤
      (CompressLoop.preparedStream first capacity n).avail_out.toNat := by
    rw [fullInput]
    simp only [CompressLoop.preparedStream,outAvail,beq_self_eq_true,ite_true,CompressChunks.chunk_value]
    exact Nat.le_min.mpr ⟨room,boundFit⟩
  obtain ⟨produced,after,za,da,engineRun,goodA,_buffersA,account,budget,_inputZero,_status,_wrap,_pending,_look,_bits⟩ :=
    public_first_finish_compress_bound start level boundary buffers pointerP encodingP.protocol.configuration.memory valid outputRoom
  have bodyRun : body (some (.tab slot)) (Z_OK,capacity,n) h =
      .ok ((Z_STREAM_END,(prepare h slot first capacity n).1,0),after) := by
    rw [body_prepare h slot first Z_OK capacity n get]
    change deflate (some (.tab slot)) Z_FINISH (prepare h slot first capacity n).2.2 = .ok (Z_STREAM_END,after) at engineRun
    rcases eq : prepare h slot first capacity n with ⟨l,p,hp⟩
    simp only [eq] at pendingZero engineRun ⊢
    rw [pendingZero]
    simp only [show ((0 : UInt64) != 0) = false from rfl,Bool.false_eq_true,ite_false,bind_app,engineRun,pure_app]
  have loopRun : loop (some (.tab slot)) (Z_OK,capacity,n) h =
      .ok ((Z_STREAM_END,(prepare h slot first capacity n).1,0),after) := by
    rw [loop_unfold]
    simp only [bind_app,bodyRun,show (Z_STREAM_END == Z_OK) = false from rfl,Bool.false_eq_true,ite_false,pure_app]
  have execution : ActualPrefix slot h (Z_OK,capacity,n) 1 after (Z_STREAM_END,(prepare h slot first capacity n).1,0) :=
    ActualPrefix.step .nil rfl bodyRun
  obtain ⟨used,log,observed,sound⟩ := actual_prefix_sound history get ranges pointer execution
  have streams : za = observed := Option.some.inj (goodA.live.hz.symm.trans sound.get)
  subst za
  have counts := (prepare_counts h slot first capacity n).1
  change (prepare h slot first capacity n).1.toNat + (CompressLoop.preparedStream first capacity n).avail_out.toNat = _ at counts
  have accountOut := account.2.2.2.1
  have observedOut := sound.outputCount
  dsimp only at observedOut
  have producedEq : produced = log.output.length := by omega
  rw [fullInput,producedEq] at budget
  exact ⟨after,(prepare h slot first capacity n).1,used,log,observed,loopRun,sound,budget⟩

/-- Actual successful initialization plus sufficient advertised capacity
makes the entire real small-source wrapper return OK within that bound.
The returned physical output and scalar include the real pointer difference,
End and automatic-stream free. -/
theorem sufficient_small_capacity {h initialized : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (small : xs.length < 2^25) (room : Api.compressBound xs.length ≤ capacity.toNat)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized)) :
    ∃ output after,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h =
        .ok ((Z_OK,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      output.length ≤ Api.compressBound xs.length := by
  obtain ⟨ready,first,setup,history,get,ranges,out,_in,outAvail,inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have setupFrame := setup_frame fresh unique globals actualInit setup
  have globalsReady : LibraryGlobals ready := setupFrame.1.symm.trans globals
  have raw := out.trans pointer
  obtain ⟨loopHeap,left,used,log,returned,loopRun,sound,budget⟩ :=
    first_loop_bound history get globalsReady ranges raw inAvail outAvail small room
  obtain ⟨buffers,_snapshot⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
  have cursor : returned.next_out = .ref (.blk ob) (oo+log.output.length) := by rw [sound.outputPtr,raw];rfl
  have physical : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by rw [←raw];exact sound.outputBytes
  have smallOutput : log.output.length < 2^63 := by have fit := (small_bound_fits small).2;omega
  obtain ⟨ds,d,after,_good,tailRun,finalBytes,_dead,_live,_frame,_count,_next,word⟩ :=
    tail_nonnull_exact sound.history sound.get buffers cursor physical smallOutput Z_STREAM_END
  simp only [beq_self_eq_true,ite_true] at tailRun
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have whole := run_of_successful_stages fresh bytes nonnull actualInit setup loopRun (by rw [pointer];exact tailRun)
  exact ⟨log.output,after,whole,word,by rw [pointer];exact finalBytes,budget⟩

/-- The small-source API relation follows from real return semantics plus
the two independently proved capacity clauses. Argument guards retain the
actual null-input convention and the actual scalar writeback. -/
theorem small_api_relation {h : Heap} {dest source : BPtr} {capacity n : UInt64} {xs output : List UInt8} {after : Heap} {rc : Int32}
    (bytes : Bytes h source n.toNat xs) (nonnull : dest ≠ .null)
    (word : (UInt64.ofNat output.length).toNat = output.length)
    (fits : output.length ≤ capacity.toNat) (bound : output.length ≤ Api.compressBound xs.length)
    (allowed : rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR)
    (memory : rc = Z_MEM_ERROR → output = [] ∧ AllocationFailed h after)
    (valid : rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs)
    (buffer : rc = Z_BUF_ERROR → output.length = capacity.toNat ∧
      ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete xs ∧ output <+: complete)
    (below : rc = Z_BUF_ERROR → capacity.toNat < Api.compressBound xs.length) :
    Api.Compress2Z
      {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
        sourceNull := source == .null,destNull := dest == .null,lengthNull := false}
      {rc := rc.toInt,produced := output,storedLength := (some (UInt64.ofNat output.length)).map UInt64.toNat} := by
  have sourceEmpty : (source == .null) = true → xs = [] := by
    intro null
    have ptr : source = .null := beq_iff_eq.mp null
    rw [ptr] at bytes
    rcases bytes with ⟨_,_zero,empty⟩ | ⟨_,_,_,impossible,_⟩
    · exact empty
    · cases impossible
  have rejected : ¬Api.CompressCall.rejected (
      {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
       sourceNull := source == .null,destNull := dest == .null,lengthNull := false} : Api.CompressCall) := by
    intro bad
    rcases bad with ⟨null,notEmpty⟩ | missing | ⟨null,_positive⟩
    · exact notEmpty (sourceEmpty null)
    · cases missing
    · exact nonnull (beq_iff_eq.mp null)
  have params : Api.compressParams Z_DEFAULT_COMPRESSION.toInt = some (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) := by decide +kernel
  have destination : (dest == .null) = false := beq_eq_false_iff_ne.mpr nonnull
  unfold Api.Compress2Z
  rw [ite_eq_right rejected]
  simp only [params,destination,Bool.false_eq_true,ite_false]
  refine ⟨?_,by simp only [Option.map_some,word]⟩
  simp only [Api.Compress2,Bool.true_eq_false,ite_false,params]
  rcases allowed with okay | buf | mem
  · subst rc
    exact Or.inr (Or.inl ⟨rfl,valid rfl,fits,bound⟩)
  · subst rc
    obtain ⟨fill,complete,completeValid,extension⟩ := buffer rfl
    exact Or.inr (Or.inr ⟨rfl,fill,below rfl,complete,completeValid,extension⟩)
  · subst rc
    exact Or.inl ⟨rfl,(memory rfl).1⟩

/-- The unchanged Compress2Z relation is established on the real default
raw-output small-source branch, for every legal capacity and every oracle.
It includes both numeric Bound clauses, exact Store, full caller Frame and
live ledger. The larger-source and broader public domains remain separate. -/
theorem small_wrapper_api_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (small : xs.length < 2^25) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      Api.Compress2Z
        {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
          sourceNull := source == .null,destNull := dest == .null,lengthNull := false}
        {rc := rc.toInt,produced := output,storedLength := (some (UInt64.ofNat output.length)).map UInt64.toNat} ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧ (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,word,fits,physical,store,frame,allowed,memory,valid,buffer,live,dead⟩ :=
    default_wrapper_buffer_total fresh unique globals objects bytes writable separate pointer
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have capacityClauses : output.length ≤ Api.compressBound xs.length ∧
      (rc = Z_BUF_ERROR → capacity.toNat < Api.compressBound xs.length) := by
    by_cases below : capacity.toNat < Api.compressBound xs.length
    · exact ⟨by omega,fun _ => below⟩
    · have room : Api.compressBound xs.length ≤ capacity.toNat := by omega
      obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
      obtain ⟨initRc,initialized,actualInit,initAllowed⟩ := default_initialization_total f u g get alloc v
      rcases initAllowed with okay | mem
      · subst initRc
        obtain ⟨completed,final,completedRun,completedWord,_completedBytes,budget⟩ :=
          sufficient_small_capacity fresh unique globals bytes writable separate pointer small room actualInit
        have events := Prod.mk.inj (Except.ok.inj (completedRun.symm.trans actual))
        have code := congrArg Prod.fst events.1
        have scalar := Option.some.inj (congrArg Prod.snd events.1)
        have lengths := congrArg UInt64.toNat scalar
        rw [completedWord,word] at lengths
        exact ⟨by omega,fun buf => False.elim ((by decide : Z_OK ≠ Z_BUF_ERROR) (code.trans buf))⟩
      · subst initRc
        obtain ⟨code,_scalar,_failed⟩ := memory_return_effects fresh unique globals bytes nonnull actualInit actual
        have empty := (memory code).1
        rw [empty,List.length_nil]
        exact ⟨Nat.zero_le _,fun buf => False.elim ((by decide : Z_MEM_ERROR ≠ Z_BUF_ERROR) (code.symm.trans buf))⟩
  have api := small_api_relation bytes nonnull word fits capacityClauses.1 allowed memory valid buffer capacityClauses.2
  exact ⟨rc,output,after,expected,actual,word,physical,store,frame,api,fun error => (memory error).2,live,dead⟩


/-- The four original utility entry points share the same small-source
execution, physical output and exact cleanup. The compatibility wrapper
also satisfies its unchanged nonnull-length-cell API relation. -/
theorem small_family_api_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (small : xs.length < 2^25) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress_z dest (some capacity) source n) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress2 dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      C.run (compress dest (some capacity) source n) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      Api.Compress2Wrapper
        {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
          sourceNull := source == .null,destNull := dest == .null,lengthNull := false}
        {rc := rc.toInt,produced := output,storedLength := (some (UInt64.ofNat output.length)).map UInt64.toNat} ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧ (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,word,physical,store,frame,api,memory,live,dead⟩ :=
    small_wrapper_api_total fresh unique globals objects bytes writable separate pointer small
  have compat := compatibility_run_of_z actual
  exact ⟨rc,output,after,expected,actual,actual,compat,compat,word,physical,store,frame,⟨rfl,api⟩,memory,live,dead⟩

end ZlibF.Spec.Public.Proofs.CompressSmall
