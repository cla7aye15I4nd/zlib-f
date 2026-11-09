import ZlibF.Proof.«compress.c.local-initialization»

/-! # Real initial requests with local private representation

The old DGood and Rebuffer definitions stay unchanged. The constructor
below exports only actual initialization fields from the frozen local
initializer. The real request entry and header use DLive and concrete
buffer lookups, including old caller identities with typed collisions.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalHeader
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Initialization's concrete entry fields, attached to the local state.
This is constructed from the actual initializer, not a callee assumption. -/
structure LocalStart (h : Heap) (cutoff : Nat) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  representation : LocalState h cutoff r ds z d
  status : d.status = INIT_STATE
  wrap : d.wrap = 1
  bits : d.bi_valid = 0
  level : d.level = 6
  strategy : d.strategy = 0
  window : d.w_bits = 15
  start : d.strstart = 0
  pending : d.pending = 0
  cursor : d.pending_out = d.pending_buf
  lastFlush : d.last_flush = -2
  adler : z.adler = 1

/-- Export the concrete initialized fields without rebuilding its proof.
The actual successful allocator theorem is the frozen local constructor. -/
theorem allocate_local_start {h : Heap} {r : ZStreamRef} {z : ZStream} {cutoff : Nat}
    (fresh : Fresh h) (unique : UniqueFrom h cutoff) (get : r.get h = some z) (allocator : DefAlloc z)
    (static : Zlib.Trees.Proofs.Out.TreesStatic h.static)
    (requests : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true) :
    ∃ a1 a2 a3 qa,
      allocate (some r) 6 h = .ok (Z_OK,successHeap h r z 6 a1 a2 a3 qa) ∧
      LocalStart (successHeap h r z 6 a1 a2 a3 qa) cutoff r h.nextBlk
        (resultStream h r z 6) (resultState h r 6 a1 a2 a3) := by
  obtain ⟨a1,a2,a3,qa,run,state,_live⟩ := allocate_success_local fresh unique get allocator static requests 6 (by decide) (by decide)
  refine ⟨a1,a2,a3,qa,run,state,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [resultState,resultStream,finalState,lmD,resetState,rkPost,rkPost3,rkMid,
      Zlib.Trees.Proofs.Out.ibRec,Zlib.Trees.Proofs.Out.trInitRec,readyState,allocatedState,baseState,
      publishedHeap,stateHeap,absWrap,rkZ]

/-- Four real caller-field assignments preserve the local representation
and all initialized entry controls. The old global-Uniq Rebuffer contract
is not used or weakened. -/
theorem LocalStart.bindings {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (initial : LocalStart h cutoff r ds z d) (dest source : BPtr) (ao ai : UInt32) :
    let next := { z with next_out := dest,avail_out := ao,next_in := source,avail_in := ai }
    C.run (zwr (some r) (fun _ => next)) h = .ok ((),r.put h next) ∧
      LocalStart (r.put h next) cutoff r ds next d := by
  let next := { z with next_out := dest,avail_out := ao,next_in := source,avail_in := ai }
  have localState := initial.representation
  have shape := shape_put localState.live.hz next
  have live : DLive (r.put h next) r ds next d := by
    exact ⟨ZStreamRef.get_put_same localState.live.hz _,by simpa using localState.live.hs,
      localState.live.zst,localState.live.back,localState.live.status,localState.live.zalloc,localState.live.zfree⟩
  have trees : Zlib.Trees.Proofs.Out.TreesInv (r.put h next) ds :=
    TreesInv.keep (d := d) localState.trees localState.live.hs (by simp) (by simp) (by simp)
      (by simpa using localState.live.hs) localState.inv.wf (by trkeep) localState.inv.pending_le
  have representation : LocalState (r.put h next) cutoff r ds next d :=
    ⟨live,localState.inv.congr (by simp) (by simp) (by simp) (by simp),
      localState.newUnique.shape shape,shape.fresh (by simp) localState.fresh,trees⟩
  refine ⟨?_,representation,initial.status,initial.wrap,initial.bits,initial.level,initial.strategy,
    initial.window,initial.start,initial.pending,initial.cursor,initial.lastFlush,initial.adler⟩
  simp only [C.run,zwr_eq,localState.live.hz]

/-- The real initial NO_FLUSH entry needs only live storage and concrete
initialized controls. It reaches the real zlib header after its original
checks and last_flush store, without constructing global DGood. -/
theorem local_no_flush_entry {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (initial : LocalStart h cutoff r ds z d) (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_NO_FLUSH h = publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH) (setD h ds {d with last_flush := Z_NO_FLUSH}) := by
  have live := initial.representation.live
  have checked := stateCheck_live live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have rank0 : RANK Z_NO_FLUSH = pure 0 := rfl
  have rankOld : RANK (-2) = pure (-4) := rfl
  rw [public_deflate_source]
  simp only [bind_app,pure_app,checked,show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide,show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,zrd_eq,live.hz,live.zst,castDeflateState,
    ldZStream_ok live.hz,ldDeflateState_tab live.hs,inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    initial.status,show (INIT_STATE == FINISH_STATE) = false from by decide,Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,wrD_eq,live.hs,
    initial.pending,show ((0 : UInt64) != 0) = false from rfl,initial.lastFlush,rank0,rankOld,
    show ((0 : Int32) ≤ -4) = False from by decide,Bool.and_false,rdD_eq,setD_dstates_same,ZStreamRef.get_setD]

/-- The same actual initial FINISH entry includes its actual rank/flag
checks. It also uses no old global-Uniq invariant or Rebuffer premise. -/
theorem local_finish_entry {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (initial : LocalStart h cutoff r ds z d) (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_FINISH h = publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH) (setD h ds {d with last_flush := Z_FINISH}) := by
  have live := initial.representation.live
  have checked := stateCheck_live live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have rank0 : RANK Z_FINISH = pure 8 := rfl
  have rankOld : RANK (-2) = pure (-4) := rfl
  rw [public_deflate_source]
  simp only [bind_app,pure_app,checked,show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide,show (Z_FINISH < 0) = False from by decide,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,zrd_eq,live.hz,live.zst,castDeflateState,
    ldZStream_ok live.hz,ldDeflateState_tab live.hs,inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    initial.status,show (INIT_STATE == FINISH_STATE) = false from by decide,Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,wrD_eq,live.hs,
    initial.pending,show ((0 : UInt64) != 0) = false from rfl,initial.lastFlush,rank0,rankOld,
    show (Z_FINISH != Z_FINISH) = false from rfl,
    Bool.and_false,rdD_eq,setD_dstates_same,ZStreamRef.get_setD]

/-- A first one-byte offer completes a real ordinary deflate call. The
source returns OK after publishing the first header byte and retains one
pending byte. This is a complete subcall, before any data-loop dispatch. -/
theorem local_first_one_run {h : Heap} {cutoff ds pb ob oo : Nat} {r : ZStreamRef}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {flush : Int32}
    (initial : LocalStart h cutoff r ds z d) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo+z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    let recorded := { d with last_flush := flush }
    let after := zlibHeaderFlushed (setD h ds recorded) r ds pb ob oo z recorded buf output
    let result := {pendingState (zlibHeaderState recorded) (.ref (.blk pb) 1) 1 with last_flush := -1}
    deflate (some r) flush h = .ok (Z_OK,setD after ds result) := by
  have positive : z.avail_out ≠ 0 := by rw [one];decide
  have out : z.next_out ≠ .null := by rw [pointer];intro bad;cases bad
  have entry : deflate (some r) flush h = publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) flush) (setD h ds {d with last_flush := flush}) := by
    rcases mode with rfl | rfl
    · exact local_no_flush_entry initial out positive valid
    · exact local_finish_entry initial out positive valid
  have header := public_default_header_run (h := setD h ds {d with last_flush := flush})
    (d := {d with last_flush := flush}) (by simpa using initial.representation.live.hz)
    initial.representation.live.zst (by simp) initial.status initial.wrap initial.bits initial.level
    initial.strategy initial.window initial.start initial.pending pendingPtr initial.cursor
    (by simpa using get) room (by simpa using rw) pointer (by simpa using outGet)
    (by simpa using outRw) separate outBound positive (publicDataTail (some r) (some (.tab ds)) flush)
  rw [entry,header]
  simp only [one,pendingLen,show ((2 : UInt64) > (1 : UInt32).toUInt64) = True from by decide,
    ite_true,show ((2 : UInt64) - (1 : UInt32).toUInt64 != 0) = true from rfl]
  rfl


/-- Updating an actual raw byte array preserves the local representation,
including other typed slots at the same old numeric identity. -/
theorem local_state_bytes_set {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (localState : LocalState h cutoff r ds z d) (x : Nat) (a old : Array UInt8)
    (get : h.bytes x = some old) (size : a.size = old.size) :
    LocalState {h with bytes := upd h.bytes x (some a)} cutoff r ds z d := by
  have shape := shape_setB get a
  refine ⟨⟨?_,localState.live.hs,localState.live.zst,localState.live.back,localState.live.status,
    localState.live.zalloc,localState.live.zfree⟩,localState.inv.bytes_set x a old get size (fun _ _ => rfl),
    localState.newUnique.shape shape,shape.fresh rfl localState.fresh,TreesInv.bytes_set localState.trees x a old get size⟩
  cases r <;>simpa [ZStreamRef.get] using localState.live.hz

/-- Stream/state field stores retain local type occupancy and representation.
This version constructs LocalState directly and never invents global Uniq. -/
theorem local_state_setZD {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z z' : ZStream} {d d' : DeflateState}
    (state : LocalState h cutoff r ds z d)
    (control : z'.state = z.state) (alloc : z'.zalloc ≠ .null) (free : z'.zfree ≠ .null)
    (back : d'.strm = d.strm) (status : GoodStatus d'.status) (inv : DStInv h ds d') (keep : TrKeep d d') :
    LocalState (setD (r.put h z') ds d') cutoff r ds z' d' := by
  have shape := (shape_put state.live.hz z').trans (shape_setD (by simpa using state.live.hs) d')
  refine ⟨⟨?_,by simp,control.trans state.live.zst,back.trans state.live.back,status,alloc,free⟩,
    inv.congr (by simp) (by simp) (by simp) (by simp),state.newUnique.shape shape,
    shape.fresh (by simp) state.fresh,?_⟩
  · simp [ZStreamRef.get_put,state.live.hz]
  · exact TreesInv.keep state.trees state.live.hs (by simp) (by simp) (by simp) (by simp) inv.wf keep inv.pending_le

/-- Exact normalized heap of the real first one-byte header return. -/
def oneHeaderState (d : DeflateState) : DeflateState :=
  {d with status := BUSY_STATE,pending := 1,pending_out := advance d.pending_buf 1,last_flush := -1}

def oneHeaderStream (z : ZStream) (ob oo : Nat) : ZStream :=
  pendingStream {z with adler := 1} (.ref (.blk ob) (oo+1)) 1

def oneHeaderHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  let staged := {h with bytes := (upd (upd h.bytes pb (some (zlibHeaderBytes buf))) ob (some (copyRange output (zlibHeaderBytes buf) oo 0 1)))}
  setD (r.put staged (oneHeaderStream z ob oo)) ds (oneHeaderState d)

/-- The real first ordinary one-byte subcall returns its exact normalized
heap and establishes the next local state. All other typed tables are kept
by their actual stores, not inferred from global owner uniqueness. -/
theorem local_first_one_state {h : Heap} {cutoff ds pb ob oo : Nat} {r : ZStreamRef}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {flush : Int32}
    (initial : LocalStart h cutoff r ds z d) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (rw : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo+z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) flush h = .ok (Z_OK,oneHeaderHeap h r ds pb ob oo z d buf output) ∧
    LocalState (oneHeaderHeap h r ds pb ob oo z d buf output) cutoff r ds
      (oneHeaderStream z ob oo) (oneHeaderState d) := by
  have actual := local_first_one_run initial mode pendingPtr get room rw pointer outGet outRw separate outBound one valid
  have normalize :
    (let recorded := {d with last_flush := flush}
     let after := zlibHeaderFlushed (setD h ds recorded) r ds pb ob oo z recorded buf output
     let result := {pendingState (zlibHeaderState recorded) (.ref (.blk pb) 1) 1 with last_flush := -1}
     setD after ds result) = oneHeaderHeap h r ds pb ob oo z d buf output := by
    simp only [zlibHeaderFlushed,one,pendingLen,show ((2 : UInt64) > (1 : UInt32).toUInt64) = True from by decide,
      ite_true,zlibHeaderReady,setD_bytes,ZStreamRef.put_bytes,setD_bytes_commute,←stream_put_bytes,ZStreamRef.put_setD,setD_setD,
      ZStreamRef.put_put,oneHeaderHeap,oneHeaderStream,oneHeaderState,pendingState,zlibHeaderState,
      show ((2 : UInt64)-(1 : UInt32).toUInt64) = 1 from rfl,
      show ((1 : UInt64) == 0) = false from rfl,Bool.false_eq_true,ite_false,initial.cursor,pendingPtr,advance]
    rfl
  dsimp only at actual normalize
  rw [normalize] at actual
  have first := local_state_bytes_set initial.representation pb (zlibHeaderBytes buf) buf get (by simp [zlibHeaderBytes])
  have second := local_state_bytes_set first ob (copyRange output (zlibHeaderBytes buf) oo 0 1) output
    (by simpa only [upd_ne _ _ _ _ separate] using outGet) (size_copyRange _ _ _ _ _)
  obtain ⟨w,p,q,b,blocks⟩ := second.inv.blocks
  have pendingId : b = pb := by
    have eq := blocks.pbuf.symm.trans pendingPtr
    exact BRef.blk.inj (Ptr.ref.inj eq).1
  subst b
  have blocksA : DBlocks _ (oneHeaderState d) w p q pb :=
    {blocks with pout := ⟨1,by simp [oneHeaderState,pendingPtr,advance],by
      change 1+1 ≤ d.pending_buf_size.toNat
      have size := blocks.psize
      obtain ⟨buffer,getBuffer,bufferSize⟩ := blocks.ba
      have lower := initial.representation.trees
      obtain ⟨old,pb0,buf0,trees⟩ := lower
      have dEq : old = d := Option.some.inj (trees.base.dstate.symm.trans initial.representation.live.hs)
      subst old
      have lower := trees.base.lit_lo
      omega⟩}
  have inv : DStInv _ ds (oneHeaderState d) := {second.inv with blocks := ⟨w,p,q,pb,blocksA⟩}
  have next := local_state_setZD second (z' := oneHeaderStream z ob oo) (d' := oneHeaderState d)
    rfl initial.representation.live.zalloc initial.representation.live.zfree rfl
    (by simp [GoodStatus,oneHeaderState]) inv (by trkeep)
  exact ⟨actual,next⟩


/-- Normalize only the actual raw output bytes. Every old typed slot at
that same numeric owner is retained by the actual header's typed stores.
No type-uniqueness premise at an old caller owner is needed. -/
theorem one_header_old_slots {h : Heap} {cutoff slot ds pb ob oo : Nat} {z : ZStream} {d : DeflateState}
    {buf output : Array UInt8} (get : h.streams slot = some z) (outGet : h.bytes ob = some output)
    (streamNew : cutoff ≤ slot) (stateNew : cutoff ≤ ds) (pendingNew : cutoff ≤ pb)
    {x : Nat} (old : x < cutoff) :
    SlotSame h (Zlib.Trees.Proofs.Out.setB (oneHeaderHeap h (.tab slot) ds pb ob oo z d buf output) ob output) x := by
  have notStream : x ≠ slot := by omega
  have notState : x ≠ ds := by omega
  have notPending : x ≠ pb := by omega
  by_cases same : x = ob
  · subst x
    simp [SlotSame,oneHeaderHeap,Zlib.Trees.Proofs.Out.setB,ZStreamRef.put,get,upd_apply,
      notStream,notState,notPending,outGet]
  · simp [SlotSame,oneHeaderHeap,Zlib.Trees.Proofs.Out.setB,ZStreamRef.put,get,upd_apply,
      notStream,notState,notPending,same]

/-- Actual header copy accounting is exact at one output byte. -/
theorem one_header_accounting {z : ZStream} {ob oo : Nat}
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1) :
    StreamAccounting z (oneHeaderStream z ob oo) 0 1 := by
  simp only [oneHeaderStream,pendingStream]
  refine ⟨Nat.zero_le _,by rw [one];decide,by simp,?_,(advance_zero _).symm,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rw [one];rfl
  · rw [pointer];rfl

/-- The original caller byte snapshot and Fresh allocation cutoff separate
raw output from the newly created stream/state/pending identities, while
allowing other typed tables at the old raw-output owner. -/
theorem original_output_before_private {h : Heap} {ob oo cutoff pb slot ds : Nat} {n : Nat}
    (fresh : Fresh h) (writable : Writable h (.ref (.blk ob) oo) n)
    (cutoffEq : cutoff = h.nextBlk) (pendingNew : cutoff ≤ pb) (streamNew : cutoff ≤ slot) (stateNew : cutoff ≤ ds) :
    ob < cutoff ∧ ob ≠ pb ∧ ob ≠ slot ∧ ob ≠ ds := by
  rcases writable with ⟨impossible,_⟩ | ⟨ref,offset,array,equal,get,_rw,_bound⟩
  · cases impossible
  · obtain ⟨sameRef,sameOffset⟩ := Ptr.ref.inj equal
    subst ref offset
    have live : h.live ob := by simp [Heap.live,show h.bytes ob = some array from get]
    have old := fresh.lt live
    omega


/-- The normalized actual first-header heap contains byte 0x78 at the
caller output, independently of old typed slots at that allocation owner. -/
theorem one_header_physical {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (room : 2 ≤ buf.size) (outputRoom : oo+1 ≤ output.size) :
    Bytes (oneHeaderHeap h r ds pb ob oo z d buf output) (.ref (.blk ob) oo) 1 [120] := by
  have first : (zlibHeaderBytes buf)[0]? = some (120 : UInt8) := by
    simp [zlibHeaderBytes,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,show 0 < buf.size by omega]
  have copied : (copyRange output (zlibHeaderBytes buf) oo 0 1)[oo]? = some (120 : UInt8) := by
    rw [getElem?_copyRange output (zlibHeaderBytes buf) oo 0 1 oo outputRoom]
    simp [getElem!_def,first]
  have slice := ZlibF.Math.DeflateEncoding.array_one_slice (array := copyRange output (zlibHeaderBytes buf) oo 0 1)
    (offset := oo) (by rw [size_copyRange];omega) copied
  exact Or.inr ⟨.blk ob,oo,copyRange output (zlibHeaderBytes buf) oo 0 1,rfl,
    by simp [oneHeaderHeap],by rw [size_copyRange];exact outputRoom,slice.symm⟩

/-- The original Fresh caller heap produces the local first-request
entry controls through the real automatic stream and complete initializer.
The frame and private-key placement are derived from that actual run. -/
theorem fresh_local_start {h : Heap} (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true) :
    ∃ after z d,
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalStart after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      d.pending_buf = .ref (.blk (h.nextBlk+5)) 0 ∧ Frame h after (fun _ => False) := by
  let root := ZStreamRef.tab h.nextBlk
  let automatic := ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h
  let old := ZlibF.Spec.Public.Proofs.CompressCaller.localStream h
  let z := ZlibF.Spec.Public.preparedStream old
  let prepared := root.put automatic z
  have get : root.get automatic = some old := by
    simp [root,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,ZStreamRef.get,old]
  obtain ⟨freshA,uniqueA⟩ := automatic_stream_local fresh
  have controls := shape_put get z
  have freshP : Fresh prepared := controls.fresh (by simp) freshA
  have uniqueP : UniqueFrom prepared h.nextBlk := uniqueA.shape controls
  have getP : root.get prepared = some z := ZStreamRef.get_put_same get _
  have allocator : DefAlloc z := by
    simp [DefAlloc,z,ZlibF.Spec.Public.preparedStream,old,ZlibF.Spec.Public.Proofs.CompressCaller.localStream]
  have static : Zlib.Trees.Proofs.Out.TreesStatic prepared.static := by
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals
  have requests : ∀ j, j < 5 → prepared.allocOk (prepared.nalloc+j) = true := by
    intro j bound
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using allocations j bound
  obtain ⟨a1,a2,a3,qa,run,start⟩ := allocate_local_start freshP uniqueP getP allocator static requests
  let after := successHeap prepared root z 6 a1 a2 a3 qa
  have version : VersionValue automatic (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have init := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize,show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide +kernel] at init
  change deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 automatic = allocate (some root) 6 prepared at init
  have next : prepared.nextBlk = h.nextBlk+1 := by simp [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap]
  obtain ⟨computed,_zi,_di,actualI,_local,frame,_live⟩ := fresh_utility_initialization fresh globals allocations
  have actual : C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) automatic = .ok (Z_OK,after) := init.trans run
  have same : computed = after := (Prod.mk.inj (Except.ok.inj (actualI.symm.trans actual))).2
  subst computed
  refine ⟨after,resultStream prepared root z 6,resultState prepared root 6 a1 a2 a3,actual,?_,?_,frame⟩
  · simpa only [next] using start
  · simp [resultState,finalState,lmD,resetState,rkPost,rkPost3,rkMid,Zlib.Trees.Proofs.Out.ibRec,
      Zlib.Trees.Proofs.Out.trInitRec,readyState,allocatedState,baseState,next,Nat.add_assoc]

/-- Real Fresh initialization followed by one real ordinary request with
one output byte. The output's old typed owner may have other live slots.
The result is the actual complete deflate call and a new local invariant. -/
theorem fresh_first_one_call {h : Heap} {ob oo : Nat} {source : BPtr} {ai : UInt32} {flush : Int32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 1)
    (input : ai ≠ 0 → source ≠ .null) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) :
    ∃ initialized z d ready buf output,
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,initialized) ∧
      LocalStart initialized h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      C.run (zwr (some (.tab h.nextBlk)) (fun s => {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai})) initialized = .ok ((),ready) ∧
      deflate (some (.tab h.nextBlk)) flush ready =
        .ok (Z_OK,oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
          {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output) ∧
      LocalState (oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
        {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output)
        h.nextBlk (.tab h.nextBlk) (h.nextBlk+1)
        (oneHeaderStream {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} ob oo)
        (oneHeaderState d) ∧
      Bytes (oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
        {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output)
        (.ref (.blk ob) oo) 1 [120] ∧
      Frame h (Zlib.Trees.Proofs.Out.setB
        (oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
          {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output) ob output)
        (fun _ => False) := by
  obtain ⟨initialized,z,d,actualInit,start,pending,initFrame⟩ := fresh_local_start fresh globals allocations
  let next := {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}
  let ready := (ZStreamRef.tab h.nextBlk).put initialized next
  have getI : initialized.streams h.nextBlk = some z := start.representation.live.hz
  obtain ⟨setup,nextStart⟩ := start.bindings (.ref (.blk ob) oo) source 1 ai
  have getReady : ready.streams h.nextBlk = some next := nextStart.representation.live.hz
  rcases writable with ⟨impossible,_⟩ | ⟨ref,off,output,equal,getOutput,outRw,bound⟩
  · cases impossible
  obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj equal
  subst ref off
  have oldLive : h.live ob := by simp [Heap.live,show h.bytes ob = some output from getOutput]
  have oldKey := fresh.lt oldLive
  have oldSlot := initFrame.2.2.2.2.2 ob oldLive (by simp)
  have getOut : ready.bytes ob = some output := by simpa only [ready,ZStreamRef.put_bytes] using oldSlot.1.trans getOutput
  have writableOut : ready.ro ob = false := by simpa only [ready,ZStreamRef.put_ro] using oldSlot.2.2.2.2.2.2.2.trans outRw
  obtain ⟨oldD,pb,buf,trees⟩ := nextStart.representation.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans nextStart.representation.live.hs)
  subst oldD
  have samePending : pb = h.nextBlk+5 := BRef.blk.inj (Ptr.ref.inj (trees.base.pbuf.symm.trans pending)).1
  subst pb
  have pendingRoom : 2 ≤ buf.size := by have size := trees.base.size;have lo := trees.base.lit_lo;omega
  obtain ⟨actualCall,stateA⟩ := local_first_one_state nextStart mode pending trees.base.bytes pendingRoom trees.base.rw
    (show next.next_out = .ref (.blk ob) oo from rfl) getOut writableOut (by omega)
    (show oo+next.avail_out.toNat ≤ output.size from bound) (show next.avail_out = 1 from rfl) input
  refine ⟨initialized,z,d,ready,buf,output,actualInit,start,?_,actualCall,stateA,one_header_physical pendingRoom bound,?_⟩
  · simp only [C.run,zwr_eq,show ZStreamRef.get initialized (.tab h.nextBlk) = some z from getI,next,ready]
  · have frameReady : Frame h ready (fun _ => False) := by
      refine ⟨by simpa [ready] using initFrame.1,by simpa [ready] using initFrame.2.1,by simpa [ready] using initFrame.2.2.1,?_,?_,?_⟩
      · simpa [ready] using initFrame.2.2.2.1
      · simpa [ready] using initFrame.2.2.2.2.1
      · intro x live _outside
        have low := fresh.lt live
        have same : x ≠ h.nextBlk := by omega
        have first : SlotSame h initialized x := initFrame.2.2.2.2.2 x live (by simp)
        exact first.trans (slot_put_except initialized (.tab h.nextBlk) next x same)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [oneHeaderHeap,Zlib.Trees.Proofs.Out.setB] using frameReady.1
    · simpa [oneHeaderHeap,Zlib.Trees.Proofs.Out.setB] using frameReady.2.1
    · simpa [oneHeaderHeap,Zlib.Trees.Proofs.Out.setB] using frameReady.2.2.1
    · simpa [oneHeaderHeap,Zlib.Trees.Proofs.Out.setB] using frameReady.2.2.2.1
    · simpa [oneHeaderHeap,Zlib.Trees.Proofs.Out.setB] using frameReady.2.2.2.2.1
    · intro x live _outside
      have first : SlotSame h ready x := frameReady.2.2.2.2.2 x live (by simp)
      exact first.trans (one_header_old_slots getReady getOut (Nat.le_refl _) (by omega) (by omega) (fresh.lt live))

end ZlibF.Spec.Public.Proofs.CompressLocalHeader
