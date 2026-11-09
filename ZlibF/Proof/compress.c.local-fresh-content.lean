import ZlibF.Proof.«compress.c.local-content»
import ZlibF.Proof.«compress.c.local-data-history»

/-! # Actual Fresh initialization and source offer establish local content -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalFreshContent
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Every nonempty uInt first offer on this raw-source/separate-raw-output
branch has an actual init/header/rebuffer/first-refill history establishing
content against the original caller bytes. All internal invariants are
constructed here. The public continuation is explicitly anchored; this is
not a returned whole-call or FINISH theorem. -/
theorem fresh_first_content {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8} {ai : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib = some ia)
    (sourceBound : io+ai.toNat ≤ ia.size) (nonzero : ai ≠ 0) (separate : ib ≠ ob) :
    ∃ before recorded filled offered next result,
      splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) ai
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),before) ∧
      (ZStreamRef.tab h.nextBlk).get before = some offered ∧
      C.run (wr (some (.tab (h.nextBlk+1))) (fun d => {d with last_flush := Z_NO_FLUSH})) before = .ok ((),recorded) ∧
      fill_window (some (.tab (h.nextBlk+1))) recorded = .ok ((),filled) ∧
      LocalContent filled h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) next result
        (fun i => bfn ia (io+i)) 0 0 [] ∧
      StreamAccounting offered next (rbLen ai 65536).toNat 0 ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before =
        (do let bstate ← deflate_slow (some (.tab (h.nextBlk+1))) Z_NO_FLUSH
            publicStrategyReturn (some (.tab h.nextBlk)) (some (.tab (h.nextBlk+1))) Z_NO_FLUSH bstate) recorded ∧
      (262 ≤ ai.toNat → deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before =
        (do let bstate ← deflate_slow (some (.tab (h.nextBlk+1))) Z_NO_FLUSH
            publicStrategyReturn (some (.tab h.nextBlk)) (some (.tab (h.nextBlk+1))) Z_NO_FLUSH bstate) filled) := by
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  obtain ⟨header,z,d,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,
      _source,_input,_out,_zero,getInput⟩ :=
    fresh_header_source_ready (io := io) (n := ai) fresh globals allocations writableTwo inputBytes separate
  let offered := {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := ai}
  let before := (ZStreamRef.tab h.nextBlk).put header offered
  obtain ⟨setup,stateR,chainsR,fieldsR,controlsR,symbolsR,_frame⟩ :=
    local_data_rebuffer state chains fields controls symbols (.ref (.blk ob) (oo+2)) (.ref (.blk ib) io) 1 ai
  obtain ⟨w,p,q,b,blocks⟩ := stateR.inv.blocks
  obtain ⟨wa,getWindow,windowSize⟩ := blocks.wa
  have wid : w = h.nextBlk+2 := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans controlsR.2.2.2.2.2.1)).1
  subst w
  have windowSize : wa.size = 65536 := by rw [fieldsR.2.2.2.2.1] at windowSize;exact windowSize
  let ds := h.nextBlk+1
  let recordedD := {d with last_flush := Z_NO_FLUSH}
  let recorded := setD before ds recordedD
  have state0 := local_last_flush stateR Z_NO_FLUSH
  have chains0 : HeapChains recorded recordedD 0 := by
    obtain ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩ := chainsR
    exact ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩
  have symbols0 : SymbolBoundary recorded ds recordedD [] := by
    obtain ⟨pb,buf,trees,ledger,balance⟩ := symbolsR
    exact local_symbol_boundary_of_ledger state0 trees.base.pbuf trees.base.bytes
      (ledger.keep rfl rfl rfl rfl) balance
  have sourceInput : Space.get recorded (BRef.blk ib) = some ia := by
    change recorded.bytes ib = some ia
    simpa only [recorded,before,setD_bytes,ZStreamRef.put_bytes] using getInput
  have oldInput : ib < h.nextBlk := fresh.lt (by simp [Heap.live,inputBytes])
  have separateWindow : BRef.blk (h.nextBlk+2) ≠ BRef.blk ib := by intro equal;cases equal;omega
  have filled := first_fill_local_content state0 fieldsR chains0 symbols0 controlsR.2.2.2.2.1 controlsR.2.2.2.1
    controlsR.2.2.2.2.2.1 getWindow blocks.wro windowSize (ref := .blk ib) (io := io) (ia := ia) rfl
    sourceInput sourceBound nonzero (Or.inl separateWindow)
  obtain ⟨fill,content,account⟩ := filled
  let n := rbLen ai 65536
  let copied := copyRange wa ia 0 io n.toNat
  let fillHeap := firstFillHeap recorded (.tab h.nextBlk) ds (h.nextBlk+2) offered recordedD (.blk ib) io ia wa
  have fieldsFill : (firstFillState recordedD n copied).lookahead = n := by unfold firstFillState primeState;split <;> rfl
  have entry := local_busy_valid_nonempty_entry stateR.live busy pending
    (by change (Ptr.ref (BRef.blk ob) (oo+2) : BPtr) ≠ .null;intro bad;cases bad)
    (by change (1 : UInt32) ≠ 0;decide)
    (by intro _;change (Ptr.ref (BRef.blk ib) io : BPtr) ≠ .null;intro bad;cases bad)
    (by rw [last];decide) (by rw [last];decide) nonzero Z_NO_FLUSH (by decide) (by decide)
  have dispatch := public_busy_no_flush_slow_source state0.live.hz state0.live.hs busy
    fieldsR.2.2.2.2.2.2.2.1 fieldsR.2.2.2.2.2.2.2.2 (Or.inl nonzero)
  have publicSource : deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before =
      (do let bstate ← deflate_slow (some (.tab ds)) Z_NO_FLUSH
          publicStrategyReturn (some (.tab h.nextBlk)) (some (.tab ds)) Z_NO_FLUSH bstate) recorded := by
    rw [entry,dispatch]
  have offeredRun : splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) ai
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),before) := by
    simp only [C.run] at setup
    unfold splitHeaderOffer
    simp only [bind_app,prefixRun,setup]
    rfl
  have recordRun : C.run (wr (some (.tab ds)) (fun d => {d with last_flush := Z_NO_FLUSH})) before =
      .ok ((),recorded) := by
    have getRecord : before.dstates ds = some d := stateR.live.hs
    change wr (some (.tab ds)) (fun d => {d with last_flush := Z_NO_FLUSH}) before = _
    rw [wrD_eq,getRecord]
  refine ⟨before,recorded,fillHeap,offered,_,_,offeredRun,stateR.live.hz,recordRun,fill,content,account,publicSource,?_⟩
  intro enough
  have count := rbLen_nat ai 65536
  change n.toNat = min ai.toNat 65536 at count
  have readReady : ¬(firstFillState recordedD n copied).lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt,fieldsFill]
    change ¬n.toNat < 262
    omega
  have prepend := slow_call_prepend_fill state0.live.hs fieldsR.2.1 fill content.state.live.hs readReady Z_NO_FLUSH
  have prepend' : deflate_slow (some (.tab ds)) Z_NO_FLUSH recorded =
      deflate_slow (some (.tab ds)) Z_NO_FLUSH fillHeap := prepend
  rw [publicSource,bind_app,bind_app,prepend']

end ZlibF.Spec.Public.Proofs.CompressLocalFreshContent
