import ZlibF.Proof.«compress.c.store»

/-! # The real zero-capacity compressor accepts every nonnull writable byte view

The path exits on the first actual deflate refusal. It does not use the
raw-output-only engine data trace or require a per-object size bound.
-/
namespace ZlibF.Spec.Public.Proofs.CompressZero
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressLoop
open ZlibF.Spec.Public.Proofs.CompressTail ZlibF.Spec.Public.Proofs.CompressMemory
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Nonnull same-object subtraction at an unchanged cursor is zero,
including both cursors one-past. No NULL-NULL model convention is used. -/
theorem writable_zero_difference {h : Heap} {p : BPtr}
    (writable : Writable h p 0) (nonnull : p ≠ .null) : ptrDiff p p h = .ok (0,h) := by
  rcases writable with ⟨null,_⟩ | ⟨ref,off,a,pointer,get,_ro,bound⟩
  · exact False.elim (nonnull null)
  · subst p
    have guard : ((Ptr.ref ref off == (.null : BPtr)) && (Ptr.ref ref off == (.null : BPtr))) = false := rfl
    have rule := Ptr.diff_ok (o1 := off) (o2 := off) get (by omega) (by omega) (by omega)
    simpa only [OkOn,ptrDiff,guard,Bool.false_eq_true,ite_false,Int.sub_self,show Int64.ofInt 0 = 0 from by decide +kernel] using rule

/-- An exact caller frame retains every original byte view, including a
foreign deflate depth field; static and literal views retain their content. -/
theorem frame_view {h after : Heap} {ref : BRef} {a : Array UInt8}
    (frame : Frame h after (fun _ => False)) (get : Space.get h ref = some a) :
    Space.get after ref = some a := by
  cases ref with
  | blk b =>
    have live : h.live b := by simp [Heap.live,show h.bytes b = some a from get]
    exact ((frame.2.2.2.2.2 b live (fun bad => bad)).1).trans get
  | dstate_depth b =>
    cases old : h.dstates b with
    | none => simp [Space.get,old] at get
    | some d =>
      have live : h.live b := by simp [Heap.live,old]
      have kept := (frame.2.2.2.2.2 b live (fun bad => bad)).2.2.2.2.1
      change (after.dstates b).map (·.depth) = some a
      rw [kept]
      exact get
  | str i => exact get
  | st_dist_code => change some after.static.dist_code = some a; rw [←frame.1]; exact get
  | st_length_code => change some after.static.length_code = some a; rw [←frame.1]; exact get

private theorem framed_empty_bytes {h after : Heap} {p : BPtr}
    (frame : Frame h after (fun _ => False)) (writable : Writable h p 0) : Bytes after p 0 [] := by
  rcases writable with ⟨null,_⟩ | ⟨ref,off,a,pointer,get,_ro,bound⟩
  · exact Or.inl ⟨null,rfl,rfl⟩
  · exact Or.inr ⟨ref,off,a,pointer,frame_view frame get,bound,by simp⟩

private theorem guard_false {h : Heap} {source dest : BPtr} {n : UInt64} {xs : List UInt8}
    (bytes : Bytes h source n.toNat xs) :
    ((n>0 && source == .null) || ((0 : UInt64)>0 && dest == .null)) = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  have cases : n>0 ∧ source = .null := by
    simpa only [show ((0 : UInt64)>0) = False from by decide +kernel,decide_false,Bool.false_and,Bool.or_false,
      Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using bad
  obtain ⟨positive,null⟩ := cases
  rw [null] at bytes
  rcases bytes with ⟨_,zero,_⟩ | ⟨_,_,_,impossible,_⟩
  · have gt := UInt64.lt_iff_toNat_lt.mp positive
    change 0 < n.toNat at gt
    omega
  · cases impossible

private theorem local_frame (h : Heap) : Frame h (localHeap h) (StreamRoot (.tab h.nextBlk)) := by
  refine ⟨rfl,rfl,rfl,by simp [localHeap],by simp [localHeap],?_⟩
  intro b _live outside
  have different : b ≠ h.nextBlk := outside
  simp [SlotSame,localHeap,upd_ne _ _ _ _ different]

private theorem release_frame (h : Heap) (slot : Nat) : Frame h (releaseLocal h slot) (StreamRoot (.tab slot)) := by
  refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
  intro b _live outside
  have different : b ≠ slot := outside
  simp [SlotSame,releaseLocal,upd_ne _ _ _ _ different]

private theorem local_live (h : Heap) (b : Nat) :
    (localHeap h).live b ↔ h.live b ∨ b = h.nextBlk := by
  by_cases same : b = h.nextBlk
  · subst b; simp [localHeap,Heap.live]
  · simp only [localHeap,Heap.live,upd_ne _ _ _ _ same,same,or_false]

/-- Directly reuse the proved real End and free operations on the actual
returned representation. A zero pointer difference is established by
nonnull view geometry separately. No raw-output/history contract is assumed. -/
theorem good_tail_zero {h : Heap} {slot ds : Nat} {z : ZStream} {d : DeflateState} {dest : BPtr}
    (good : DGood h (.tab slot) ds z d) (alloc : DefAlloc z) (cursor : z.next_out = dest)
    (difference : ptrDiff dest dest h = .ok (0,h)) :
    ∃ after, tail (some (.tab slot)) dest Z_BUF_ERROR h = .ok ((Z_BUF_ERROR,some 0),after) ∧
      Frame h after (fun b => b = slot ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun b => DeflateOwned ds d b ∨ b = slot) ∧
      after.streams slot = none ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ended,endRun,getEnd,liveEnd,frameEnd,count,next⟩ :=
    DeflateEndProof.deflate_end_public h (.tab slot) ds z d good alloc.2
  obtain ⟨w,p,q,b,blocks⟩ := good.inv.blocks
  have canonical := deflateEnd_run good.live alloc.2 blocks
  have endEq : ended = endHeap h (.tab slot) ds z d := by
    have events : (.ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK),ended) : Except Fault (Int32×Heap)) =
        .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),endHeap h (.tab slot) ds z d) := endRun.symm.trans canonical
    exact (Prod.mk.inj (Except.ok.inj events)).2
  have uniqueEnd : Uniq ended := by rw [endEq]; exact endHeap_uniq blocks good.uniq good.live.hz
  have endedStream : ended.streams slot = some {z with state := none} := getEnd
  refine ⟨releaseLocal ended slot,?_,?_,?_,by simp [releaseLocal],count,next⟩
  · change deflateEnd (some (.tab slot)) h = _ at endRun
    have get : h.streams slot = some z := good.live.hz
    simp only [tail,bind_app,zrd_eq,ZStreamRef.get,get,pure_app,cursor,difference,endRun]
    simp [freeZStream,endedStream,releaseLocal,show Z_BUF_ERROR ≠ Z_STREAM_END from by decide +kernel,
      show (0 : Int64).toUInt64 = (0 : UInt64) from by decide +kernel]
  · exact CompressMemory.frame_trans frameEnd (full_frame_weaken (release_frame ended slot) (fun _ root => Or.inl root))
  · intro b
    rw [release_local_live uniqueEnd endedStream b,liveEnd b]
    simp only [LiveChange,not_false_eq_true,or_false,not_or,and_assoc]

/-- The zero-capacity early failure branch is independent of the output
view kind. Original caller records survive rollback and the actual free. -/
theorem zero_memory_return {h initialized : Heap} {dest source : BPtr} {n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_MEM_ERROR,initialized)) :
    ∃ after, C.run (compress2_z dest (some 0) source n Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_MEM_ERROR,some 0),after) ∧ Frame h after (fun _ => False) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none ∧ after.nalloc = initialized.nalloc := by
  obtain ⟨f,u,g,v,old,oldGet,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  have shape := memory_failure_shape f u g oldGet alloc v actualInit
  have present := (shape h.nextBlk).2.2.1
  change (initialized.streams h.nextBlk).isSome = ((localHeap h).streams h.nextBlk).isSome at present
  simp only [localHeap,upd_same,Option.isSome_some] at present
  obtain ⟨z,get⟩ : ∃z,initialized.streams h.nextBlk = some z := by
    cases eq : initialized.streams h.nextBlk with
    | none => simp only [eq,Option.isSome_none,Bool.false_eq_true] at present
    | some z => exact ⟨z,rfl⟩
  let after := releaseLocal initialized h.nextBlk
  have automatic : preInit h = .ok ((some (.tab h.nextBlk),.ref (.str 57) 0),localHeap h) := automatic_stream_run h fresh
  have free : freeZStream (some (.tab h.nextBlk)) initialized = .ok ((),after) := by
    simp [freeZStream,get,after,releaseLocal]
  have guard := guard_false (dest := dest) bytes
  have whole : C.run (compress2_z dest (some 0) source n Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_MEM_ERROR,some 0),after) := by
    rw [compress2_z_stages]
    change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
    simp only [C.run,sizeof_z_stream,guard,Bool.false_eq_true,ite_false,bind_app,automatic,actualInit,
      show (Z_MEM_ERROR != Z_OK) = true from rfl,ite_true,free,pure_app]
  have frameI := initialization_failure_frame f u g oldGet alloc v actualInit
  have total := CompressMemory.frame_trans (local_frame h) (CompressMemory.frame_trans frameI (release_frame initialized h.nextBlk))
  have frame : Frame h after (fun _ => False) := by
    refine ⟨total.1,total.2.1,total.2.2.1,total.2.2.2.1,total.2.2.2.2.1,?_⟩
    intro b live _outside
    exact total.2.2.2.2.2 b live (by intro same;change b = h.nextBlk at same;subst b;exact fresh _ (Nat.le_refl _) live)
  refine ⟨after,whole,frame,?_,by simp [after,releaseLocal],rfl⟩
  intro b
  rw [release_local_live (shape.uniq u) get,shape.live,local_live]
  constructor
  · intro now
    exact now.1.resolve_right now.2
  · intro original
    exact ⟨Or.inl original,fun eq => fresh _ (by omega) (eq ▸ original)⟩

private theorem initial_status {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (state : DefaultEncodingState h r ds z d config [] []) : d.status = INIT_STATE := by
  rcases state.phase with ⟨_input,_output,input,start,_boundary⟩ | ⟨_input,impossible,_rest⟩ |
      ⟨_input,_origin,_base,_xs,published,impossible,_rest⟩ | ⟨published,impossible,_rest⟩
  · exact start.status
  · cases impossible
  · cases impossible
  · cases impossible

/-- With real successful init, the first actual call sees zero output
capacity and returns BUF_ERROR. The wrapper then performs the real same-
object pointer subtraction, End and automatic free. Every nonnull writable
BRef and offset is included, in particular a foreign depth-field view. -/
theorem zero_success_return {h initialized : Heap} {dest source : BPtr} {n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest 0) (nonnull : dest ≠ .null)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized)) :
    ∃ after, C.run (compress2_z dest (some 0) source n Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_BUF_ERROR,some 0),after) ∧ Frame h after (fun _ => False) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none ∧
      after.nalloc = h.nalloc+5 ∧ after.nextBlk = h.nextBlk+6 := by
  obtain ⟨ready,first,setup,history,get,ranges,out,_in,outAvail,_inAvail⟩ :=
    successful_default_seed (capacity := 0) fresh unique globals bytes writable (Or.inr (Or.inl rfl)) actualInit
  obtain ⟨ds,encodingZ,d,config,encoding,_valid⟩ := history.encoding
  have firstEq : encodingZ = first := Option.some.inj (encoding.protocol.good.live.hz.symm.trans get)
  subst encodingZ
  have initialStatus : d.status = INIT_STATE := initial_status encoding
  have beforeFrame := setup_frame fresh unique globals actualInit setup
  have globalsReady : LibraryGlobals ready := beforeFrame.1.symm.trans globals
  have edit := prepare_rebuffer encoding.protocol.good globalsReady 0 n
  obtain ⟨zp,getP,boundaryP⟩ := encoding.protocol.rebuffer edit
  have zpEq : zp = CompressLoop.preparedStream first 0 n :=
    Option.some.inj (getP.symm.trans (prepare_get ready h.nextBlk first 0 n get))
  subst zp
  have rangesP := prepare_ranges encoding.protocol.good ranges
  obtain ⟨buffersP,snapshotP⟩ := ranges_current getP rangesP
  let prepared := (prepare ready h.nextBlk first 0 n).2.2
  let preparedZ := CompressLoop.preparedStream first 0 n
  let flush := if (prepare ready h.nextBlk first 0 n).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush;split <;>simp
  have low : 0 ≤ flush.toInt := by rcases flag with eq | eq <;>rw [eq] <;>decide
  have high : flush.toInt ≤ Z_BLOCK.toInt := by rcases flag with eq | eq <;>rw [eq] <;>decide
  have zeroChunk : CompressChunks.chunk (0 : UInt64) = 0 := by decide +kernel
  have empty : preparedZ.avail_out = 0 := by simp only [preparedZ,CompressLoop.preparedStream,outAvail,beq_self_eq_true,ite_true,zeroChunk]
  have cursorP : preparedZ.next_out = dest := out
  have inputValid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshotP
  have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
    intro impossible
    rw [initialStatus] at impossible
    cases impossible
  have refusalSource := public_zero_output_refusal boundaryP.good flush low high
    (by rw [cursorP];exact nonnull) inputValid finish empty
  obtain ⟨message,engineRun,boundaryA,buffersA,account⟩ := public_entry_refusal_protocol flush Z_BUF_ERROR boundaryP buffersP refusalSource
  let returned := {preparedZ with msg := message}
  let refused := (ZStreamRef.tab h.nextBlk).put prepared returned
  have refusedGet : refused.streams h.nextBlk = some returned := ZStreamRef.get_put_same getP _
  have leftP : (prepare ready h.nextBlk first 0 n).1 = 0 := by
    simp only [prepare,outAvail,_inAvail,beq_self_eq_true,ite_true,zeroChunk,
      show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl,UInt64.sub_self]

  have bodyRun : body (some (.tab h.nextBlk)) (Z_OK,0,n) ready =
      .ok ((Z_BUF_ERROR,0,(prepare ready h.nextBlk first 0 n).2.1),refused) := by
    rw [body_prepare ready h.nextBlk first Z_OK 0 n get]
    change deflate (some (.tab h.nextBlk))
      (if (prepare ready h.nextBlk first 0 n).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare ready h.nextBlk first 0 n).2.2 = .ok (Z_BUF_ERROR,refused) at engineRun
    rcases eq : prepare ready h.nextBlk first 0 n with ⟨l,nextN,hp⟩
    simp only [eq] at engineRun leftP ⊢
    simp only [bind_app,engineRun,pure_app]
    rw [leftP]
  have loopRun : loop (some (.tab h.nextBlk)) (Z_OK,0,n) ready =
      .ok ((Z_BUF_ERROR,0,(prepare ready h.nextBlk first 0 n).2.1),refused) := by
    rw [loop_unfold]
    simp only [bind_app,bodyRun,show (Z_BUF_ERROR == Z_OK) = false from rfl,Bool.false_eq_true,ite_false,pure_app]
  have returnedWritable : Writable refused dest 0 := by
    obtain ⟨actualZ,getZ,_input,output,_separate⟩ := buffersA
    have same : actualZ = returned := Option.some.inj (getZ.symm.trans refusedGet)
    subst actualZ
    have cursor : returned.next_out = dest := cursorP
    have zero : returned.avail_out = 0 := empty
    rcases output with null | ⟨_read,writable,_outside⟩
    · exact False.elim (nonnull (cursor.symm.trans null))
    · have wp : Writable refused returned.next_out returned.avail_out.toNat := writable rfl
      have zeroNat : returned.avail_out.toNat = 0 := congrArg UInt32.toNat zero
      have q := Eq.mp (congrArg (fun amount => Writable refused returned.next_out amount) zeroNat) wp
      exact Eq.mp (congrArg (fun pointer => Writable refused pointer 0) cursor) q

  obtain ⟨oldZ,getOld,alloc⟩ := history.allocators
  have allocSame : oldZ = first := Option.some.inj (getOld.symm.trans get)
  subst oldZ
  have returnedAlloc : DefAlloc returned := alloc
  have returnedCursor : returned.next_out = dest := cursorP
  have difference := writable_zero_difference returnedWritable nonnull
  obtain ⟨after,tailRun,tailFrame,tailLive,dead,tailCount,tailNext⟩ :=
    good_tail_zero boundaryA.good returnedAlloc returnedCursor difference
  have whole := run_of_successful_stages fresh bytes nonnull actualInit setup loopRun tailRun
  obtain ⟨initialZ,initialD,initial,initLive,initOwned,initCount,initNext⟩ :=
    setup_resources (dest := dest) (source := source) fresh unique globals actualInit setup
  have stateKey : ds = (localHeap h).nextBlk := StateRef.deflate.inj
    (Option.some.inj (encoding.protocol.good.live.zst.symm.trans (by
      have firstEq : initialZ = first := Option.some.inj (initial.good.live.hz.symm.trans get)
      simpa only [firstEq] using initial.good.live.zst)))
  subst ds
  have stateSame : d = initialD := Option.some.inj (encoding.protocol.good.live.hs.symm.trans initial.good.live.hs)
  subst initialD
  have shapeP : Shape ready prepared := by
    rw [show prepared = (ZStreamRef.tab h.nextBlk).put ready preparedZ from prepare_eq_put ready h.nextBlk first 0 n get]
    exact shape_put (r := .tab h.nextBlk) get _
  have shapeA : Shape prepared refused := shape_put getP returned
  have frameP : Frame ready prepared (StreamRoot (.tab h.nextBlk)) := by
    rw [show prepared = (ZStreamRef.tab h.nextBlk).put ready preparedZ from prepare_eq_put ready h.nextBlk first 0 n get]
    exact Zlib.Deflate.Proofs.DefaultInit.frame_put _ _ encoding.protocol.good.fresh
  have frameA := Zlib.Deflate.Proofs.DefaultInit.frame_put (.tab h.nextBlk) returned boundaryP.good.fresh
  let changed := fun b => b = h.nextBlk ∨ DeflateOwned (localHeap h).nextBlk d b
  have before : Frame h ready changed := full_frame_weaken beforeFrame (fun _ bad => False.elim bad)
  have middle : Frame ready refused changed := full_frame_weaken (CompressMemory.frame_trans frameP frameA) (fun _ root => Or.inl root)
  have total := CompressMemory.frame_trans before (CompressMemory.frame_trans middle tailFrame)
  have frame : Frame h after (fun _ => False) := by
    refine ⟨total.1,total.2.1,total.2.2.1,total.2.2.2.1,total.2.2.2.2.1,?_⟩
    intro b live _outside
    apply total.2.2.2.2.2 b live
    intro changedHere
    rcases changedHere with root | owned
    · exact fresh _ (by omega) (root ▸ live)
    · have low := ((initOwned b).mp owned).1
      exact fresh b (by change h.nextBlk+1 ≤ b at low;omega) live
  have ledger : ∀ b,after.live b ↔ h.live b := by
    intro b
    have initialLedger := initLive b
    have finalLedger := tailLive b
    change ready.live b ↔ ((localHeap h).live b ∧ ¬False) ∨ DeflateOwned (localHeap h).nextBlk d b at initialLedger
    change after.live b ↔ (refused.live b ∧ ¬(DeflateOwned (localHeap h).nextBlk d b ∨ b = h.nextBlk)) ∨ False at finalLedger
    rw [shapeA.live,shapeP.live,initialLedger,local_live] at finalLedger
    simp only [not_false_eq_true,and_true,or_false] at finalLedger
    have ownedDead : DeflateOwned (localHeap h).nextBlk d b → ¬h.live b := by
      intro own
      have low := ((initOwned b).mp own).1
      exact fresh b (by change h.nextBlk+1 ≤ b at low;omega)
    have rootDead : b = h.nextBlk → ¬h.live b := by intro eq;subst b;exact fresh _ (Nat.le_refl _)
    constructor
    · intro live
      rcases finalLedger.mp live with ⟨(old | root) | own,outside⟩
      · exact old
      · exact False.elim (outside (Or.inr root))
      · exact False.elim (outside (Or.inl own))
    · intro live
      exact finalLedger.mpr ⟨Or.inl (Or.inl live),fun bad => bad.elim (fun own => ownedDead own live) (fun root => rootDead root live)⟩
  refine ⟨after,whole,frame,ledger,dead,?_,?_⟩
  · rw [tailCount,ZStreamRef.put_nalloc,show prepared.nalloc = ready.nalloc from by
      rw [show prepared = (ZStreamRef.tab h.nextBlk).put ready preparedZ from prepare_eq_put ready h.nextBlk first 0 n get]
      exact ZStreamRef.put_nalloc _ _ _]
    exact initCount
  · rw [tailNext,ZStreamRef.put_nextBlk,show prepared.nextBlk = ready.nextBlk from by
      rw [show prepared = (ZStreamRef.tab h.nextBlk).put ready preparedZ from prepare_eq_put ready h.nextBlk first 0 n get]
      exact ZStreamRef.put_nextBlk _ _ _]
    exact initNext

/-- The real default init consumes one request on first-allocation failure
or five requests on buffer failure. At least one consumed oracle index
actually rejected allocation. -/
theorem memory_requests {h initialized : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_MEM_ERROR,initialized)) :
    (initialized.nalloc = h.nalloc+1 ∨ initialized.nalloc = h.nalloc+5) ∧ AllocationFailed h initialized := by
  obtain ⟨rc,computed,run,post⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version fresh unique globals get allocators valid
  have events := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  rw [events.1,events.2] at post
  change (if h.allocOk h.nalloc = false then
      Z_MEM_ERROR = Z_MEM_ERROR ∧ initialized.nalloc = h.nalloc+1 ∧ SameObjects (r.put h (ZlibF.Spec.Public.preparedStream z)) initialized
    else initialized.nalloc = h.nalloc+5 ∧
      if (List.range 5).all (fun j => h.allocOk (h.nalloc+j)) then
        Z_MEM_ERROR = Z_OK ∧ DeflateInitial h initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)
      else Z_MEM_ERROR = Z_MEM_ERROR ∧ (∃z',r.get initialized = some z' ∧ z'.state = none) ∧
        LiveChange h initialized (fun _ => False) (fun _ => False) ∧ Frame h initialized (StreamRoot r)) at post
  by_cases first : h.allocOk h.nalloc = false
  · simp only [first,ite_true] at post
    exact ⟨Or.inl post.2.1,h.nalloc,Nat.le_refl _,by omega,first⟩
  · simp only [first,ite_false] at post
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc+j)) = true
    · simp only [all,ite_true] at post
      cases post.2.1
    · have failed : (List.range 5).all (fun j => h.allocOk (h.nalloc+j)) = false := Bool.eq_false_iff.mpr all
      obtain ⟨j,member,notTrue⟩ := List.all_eq_false.mp failed
      have small := List.mem_range.mp member
      have rejected : h.allocOk (h.nalloc+j) = false := Bool.eq_false_iff.mpr notTrue
      have count := post.1
      exact ⟨Or.inr count,h.nalloc+j,by omega,by omega,rejected⟩

/-- Every nonnull writable byte view, including a foreign depth array and
one-past offsets, has the exact real zero-capacity utility return. The real
first call returns BUF_ERROR, or init returns MEM_ERROR. Both store zero
length, write no bytes and retain every original caller slot and live object.
This path needs no per-object size premise. Global Uniq remains explicit
because the reused InitDomain/default-init/DGood producer requires it. -/
theorem zero_capacity_total {h : Heap} {dest source : BPtr} {n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest 0) (nonnull : dest ≠ .null) :
    ∃ rc after, C.run (compress2_z dest (some 0) source n Z_DEFAULT_COMPRESSION) h =
      .ok ((rc,some 0),after) ∧ (rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧
      Bytes after dest 0 [] ∧ Store h dest [] h ∧ Frame h after (fun _ => False) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none ∧
      (after.nalloc = h.nalloc+1 ∨ after.nalloc = h.nalloc+5) ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨rc,initialized,actualInit,allowed⟩ := default_initialization_total f u g get alloc v
  rcases allowed with ok | memory
  · subst rc
    obtain ⟨after,actual,frame,live,dead,count,_next⟩ :=
      zero_success_return fresh unique globals bytes writable nonnull actualInit
    exact ⟨Z_BUF_ERROR,after,actual,Or.inl rfl,framed_empty_bytes frame writable,Or.inl ⟨rfl,rfl⟩,
      frame,live,dead,Or.inr count,fun impossible => False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) impossible)⟩
  · subst rc
    obtain ⟨after,actual,frame,live,dead,count⟩ := zero_memory_return (dest := dest) fresh unique globals bytes actualInit
    obtain ⟨requests,failed⟩ := memory_requests f u g get alloc v actualInit
    have originalRequests : initialized.nalloc = h.nalloc+1 ∨ initialized.nalloc = h.nalloc+5 := requests
    have originalFailure : AllocationFailed h after := by
      obtain ⟨i,lower,upper,rejected⟩ := failed
      exact ⟨i,lower,by omega,rejected⟩
    exact ⟨Z_MEM_ERROR,after,actual,Or.inr rfl,framed_empty_bytes frame writable,Or.inl ⟨rfl,rfl⟩,
      frame,live,dead,by omega,fun _ => originalFailure⟩

/-- The four real default utility entries share the same generic
zero-capacity run, exact zero writeback, complete caller frame and ledger. -/
theorem zero_capacity_family_total {h : Heap} {dest source : BPtr} {n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest 0) (nonnull : dest ≠ .null) :
    ∃ rc after,
      C.run (compress2_z dest (some 0) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some 0),after) ∧
      C.run (compress_z dest (some 0) source n) h = .ok ((rc,some 0),after) ∧
      C.run (compress2 dest (some 0) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,0),after) ∧
      C.run (compress dest (some 0) source n) h = .ok ((rc,0),after) ∧
      (rc = Z_BUF_ERROR ∨ rc = Z_MEM_ERROR) ∧ Bytes after dest 0 [] ∧ Store h dest [] h ∧
      Frame h after (fun _ => False) ∧ (∀ b,after.live b ↔ h.live b) ∧
      after.streams h.nextBlk = none ∧
      (after.nalloc = h.nalloc+1 ∨ after.nalloc = h.nalloc+5) ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  obtain ⟨rc,after,actual,allowed,physical,store,frame,live,dead,count,failed⟩ :=
    zero_capacity_total fresh unique globals bytes writable nonnull
  have compat := compatibility_run_of_z actual
  exact ⟨rc,after,actual,actual,compat,compat,allowed,physical,store,frame,live,dead,count,failed⟩

end ZlibF.Spec.Public.Proofs.CompressZero
