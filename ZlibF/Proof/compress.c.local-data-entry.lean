import ZlibF.Proof.«compress.c.local-pending-request»
import ZlibF.Proof.«deflate.c.engine.slow-first»
import ZlibF.Proof.«compress.c.local-fill»

/-! # Real BUSY entry and short-input data dispatch using local state

The source's actual state check and rank calculations are retained. Local
initialization and prior header requests supply the state; global DGood is
not used. The complete consuming branch is connected to actual local fill.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalData
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalRequest
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_busy_valid_nonempty_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (live : DLive h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) (nonempty : z.avail_in ≠ 0)
    (flush : Int32) (flushLow : 0 ≤ flush.toInt) (flushHigh : flush.toInt ≤ 5) :
    deflate (some r) flush h =
      publicDataTail (some r) (some (.tab ds)) flush
        (setD h ds { d with last_flush := flush }) := by
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) flush)
      (setD h ds { d with last_flush := flush }) =
      publicDataTail (some r) (some (.tab ds)) flush (setD h ds { d with last_flush := flush }) := by
    unfold publicZlibHeader
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live live
  obtain ⟨current, rankedCurrent⟩ := rank_legal_last_flush flush (by omega) flushHigh
  have high : ¬ flush > Z_BLOCK := by
    intro bad
    have value : 5 < flush.toInt := Int32.lt_iff_toInt_lt.mp bad
    omega
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, live.hz, live.zst, castDeflateState,
    ldZStream_ok live.hz, ldDeflateState_tab live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, live.hs, pending,
    show (z.avail_in == 0) = false from beq_eq_false_iff_ne.mpr nonempty, Bool.false_and, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankedCurrent, ranked,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  simpa only [status, pending] using header

/-- A concrete observed short fill on the actual recorded heap feeds the
real complete slow strategy and real public data return. This adapter is
about the same actual fill event, not an assumed fill specification. -/
theorem short_no_flush_of_actual_fill {h after : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z za : ZStream} {d da : DeflateState}
    (state : LocalState h cutoff r ds z d) (busy : d.status = BUSY_STATE)
    (pending : d.pending = 0) (level : d.level = 6) (strategy : d.strategy = 0)
    (empty : d.lookahead = 0) (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (nonempty : z.avail_in ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (actualFill : fill_window (some (.tab ds)) (setD h ds {d with last_flush := Z_NO_FLUSH}) = .ok ((),after))
    (stateA : LocalState after cutoff r ds za da) (short : da.lookahead < MIN_LOOKAHEAD_u)
    (account : StreamAccounting z za z.avail_in.toNat 0) :
    deflate (some r) Z_NO_FLUSH h = .ok (Z_OK,after) ∧ LocalState after cutoff r ds za da ∧
      StreamAccounting z za z.avail_in.toNat 0 ∧ za.avail_in = 0 := by
  have entry := local_busy_valid_nonempty_entry state.live busy pending out positive valid lower upper nonempty
    Z_NO_FLUSH (by decide) (by decide)
  have state0 := local_last_flush state Z_NO_FLUSH
  have slow := slow_first_short_run state0.live.hs empty actualFill stateA.live.hs short
  have dispatch := public_busy_no_flush_slow_source state0.live.hz state0.live.hs busy level strategy (Or.inl nonempty)
  have returnStep := public_need_more_return stateA.live.hz stateA.live.hs Z_NO_FLUSH
  have outputSame : za.avail_out = z.avail_out := UInt32.toNat_inj.mp (by have count := account.2.2.2.1;omega)
  have nonzeroA : za.avail_out ≠ 0 := fun zero => positive (outputSame.symm.trans zero)
  have allInput : za.avail_in = 0 := UInt32.toNat_inj.mp (by have count := account.2.2.1;change za.avail_in.toNat = 0;omega)
  refine ⟨?_,stateA,account,allInput⟩
  rw [entry,dispatch]
  simp only [bind_app,slow,returnStep,show (za.avail_out == 0) = false from beq_eq_false_iff_ne.mpr nonzeroA,
    Bool.false_eq_true,ite_false]


/-- Exact fields that select the first real non-sliding input fill. They
are extracted from actual initialization below and survive header output. -/
def InitialReadFields (d : DeflateState) : Prop :=
  d.strstart = 0 ∧ d.lookahead = 0 ∧ d.insert = 0 ∧ d.high_water = 0 ∧
  d.w_size = 32768 ∧ d.window_size = 65536 ∧ d.wrap = 1 ∧ d.level = 6 ∧ d.strategy = 0

/-- The actual observed successful initializer has first-fill controls.
Its LocalState and controls are on the same real execution, including a
caller heap with old cross-table collisions. -/
theorem initialized_read_fields {h after : Heap} {z : ZStream} {d : DeflateState}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after))
    (localState : LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d) :
    InitialReadFields d := by
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
  have computed : C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) automatic =
      .ok (Z_OK,successHeap prepared root z 6 a1 a2 a3 qa) := init.trans run
  have heaps := (Prod.mk.inj (Except.ok.inj (computed.symm.trans actualInit))).2
  have known := start.representation.live.hs
  have next : prepared.nextBlk = h.nextBlk+1 := by
    simp [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap]
  rw [heaps,next] at known
  have sameD : resultState prepared root 6 a1 a2 a3 = d := Option.some.inj (known.symm.trans localState.live.hs)
  rw [←sameD]
  simp [InitialReadFields,resultState,finalState,lmD,resetState,rkPost,rkPost3,rkMid,
    Zlib.Trees.Proofs.Out.ibRec,Zlib.Trees.Proofs.Out.trInitRec,readyState,allocatedState,baseState,absWrap]

/-- Both real header calls change only output/header control fields. The
first non-sliding read fields stay those of the actual initializer. -/
theorem read_fields_after_header {d : DeflateState} (fields : InitialReadFields d) :
    InitialReadFields (oneHeaderState d) := fields

theorem read_fields_after_pending {d : DeflateState} {out : BPtr} {n : UInt32}
    (fields : InitialReadFields d) (flush : Int32) :
    InitialReadFields {pendingState d out n with last_flush := flush} := fields

/-- A complete actual public NO_FLUSH call consumes its nonempty short
input offer. The actual local fill, actual slow loop and actual data return
are composed here. Output is any nonnull pointer: this path does not write
caller output and imposes no raw-buffer or global-Uniq restriction on it. -/
theorem local_short_no_flush {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (fields : InitialReadFields d)
    (busy : d.status = BUSY_STATE) (pending : d.pending = 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (small : z.avail_in.toNat ≤ 261)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨ io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let recorded := {d with last_flush := Z_NO_FLUSH}
    let n := rbLen z.avail_in 65536
    let copied := copyRange wa ia 0 io n.toNat
    let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let result := firstFillState recorded n copied
    let after := firstFillHeap (setD h ds recorded) r ds w z recorded ref io ia wa
    deflate (some r) Z_NO_FLUSH h = .ok (Z_OK,after) ∧ LocalState after cutoff r ds nextZ result ∧
      StreamAccounting z nextZ z.avail_in.toNat 0 ∧ nextZ.avail_in = 0 ∧
      result.lookahead = z.avail_in ∧ result.status = BUSY_STATE ∧ result.last_flush = Z_NO_FLUSH ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = w) ∧
      after.bytes w = some (fillRange copied n.toNat (firstPadding n).toNat 0) := by
  obtain ⟨ss,la,insert,high,ws,wsz,wrap,level,strategy⟩ := fields
  have state0 := local_last_flush state Z_NO_FLUSH
  obtain ⟨actualFill,stateA,account,frame,_shape,look,_strstart,status,_level,_strategy,last,bytes⟩ :=
    ZlibF.Spec.Public.Proofs.CompressLocalFill.local_fill_window_first state0 win (by simpa using get)
      (by simpa using writable) size ss la insert high ws wsz wrap pointer
      (by simpa only [byte_view_setD_depth state.live.hs (show ({d with last_flush := Z_NO_FLUSH} : DeflateState).depth = d.depth from rfl) ref] using input)
      inputBound nonempty separate
  have selected : rbLen z.avail_in 65536 = z.avail_in := UInt32.toNat_inj.mp (by
    have count := rbLen_nat z.avail_in 65536
    change (rbLen z.avail_in 65536).toNat = min z.avail_in.toNat 65536 at count
    omega)
  have accountFull : StreamAccounting z (readStream z (rbLen z.avail_in 65536) ref io
      (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat))) z.avail_in.toNat 0 := by
    simpa only [selected] using account
  have short : (firstFillState {d with last_flush := Z_NO_FLUSH} (rbLen z.avail_in 65536)
      (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat)).lookahead < MIN_LOOKAHEAD_u := by
    rw [look,selected,UInt32.lt_iff_toNat_lt]
    change z.avail_in.toNat < 262
    omega
  have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := by intro _;rw [pointer];intro bad;cases bad
  obtain ⟨actual,_state,_account,empty⟩ := short_no_flush_of_actual_fill state busy pending level strategy la out positive valid nonempty
    lower upper actualFill stateA short accountFull
  refine ⟨actual,stateA,accountFull,empty,look.trans selected,status.trans busy,last,?_,bytes⟩
  refine ⟨frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.1,?_⟩
  intro b live outside
  have notState : b ≠ ds := fun same => outside (Or.inr (Or.inl same))
  have slot := slot_setD_except h ds {d with last_flush := Z_NO_FLUSH} b notState
  apply slot.trans
  exact frame.2.2.2.2.2 b (slot.live.mpr live) outside

end ZlibF.Spec.Public.Proofs.CompressLocalData
