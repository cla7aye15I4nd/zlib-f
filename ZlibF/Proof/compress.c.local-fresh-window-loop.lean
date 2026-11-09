import ZlibF.Proof.«compress.c.local-content-loop-slide»

/-! # Fresh initialization and a real full-window offer reach the actual loop checkpoint -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalFreshWindowLoop
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Spec.Public.Proofs.CompressLocalContentLoop ZlibF.Spec.Public.Proofs.CompressLocalContentLoopSlide
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The complete ordinary prefix of the actual loop, its exact remaining
fuel, and the full real sliding refill if short lookahead is reached first.
The alternative remains the actual last-symbol-slot handling checkpoint. -/
def WindowLoopReached (h : Heap) (r : ZStreamRef) (cutoff ds origin base : Nat)
    (z : ZStream) (d : DeflateState) (input : Nat → UInt8) (xs : List Symbol) : Prop :=
  ∃ n final after result ys,
    ActualOrdinaryPrefix ds Z_NO_FLUSH n {} h final after ∧
    LocalContent after cutoff r ds z result input origin base ys ∧
    n≤d.lookahead.toNat ∧ xs<+:ys ∧ OrdinaryCheckpoint result ∧
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
    cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h=
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (fuel-n) final after ∧
    (result.lookahead.toNat<262 → ∃ used filled next continued,
      fill_window (some (.tab ds)) after=.ok ((),filled) ∧
      LocalContent filled cutoff r ds next continued input (origin+32768) base ys ∧
      StreamAccounting z next used 0 ∧ continued.strstart.toNat=result.strstart.toNat-32768 ∧
      fillEnd continued=fillEnd result-32768+used ∧
      (262≤continued.lookahead.toNat → cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h=
        cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (fuel-n) final filled))

/-- A selected real Fresh public request supplies all initial conditions
of the cumulative ordinary loop and sliding checkpoint. Source bytes are
fixed at the original ia[io+i]. No internal invariant, selected-match
quality, global Uniq or private position premise is required from callers.
This reaches the first refill/publication checkpoint, not a returned
whole utility call or the remaining full-symbol-buffer/FINISH paths. -/
theorem fresh_window_loop_checkpoint {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8} {ai : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j<5 → h.allocOk (h.nalloc+j)=true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib=some ia)
    (sourceBound : io+ai.toNat≤ia.size) (large : 65536<ai.toNat) (separate : ib≠ob) :
    ∃ before recorded filled offered next result,
      splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) ai
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok ((),before) ∧
      (ZStreamRef.tab h.nextBlk).get before=some offered ∧
      C.run (wr (some (.tab (h.nextBlk+1))) (fun d => {d with last_flush := Z_NO_FLUSH})) before=.ok ((),recorded) ∧
      fill_window (some (.tab (h.nextBlk+1))) recorded=.ok ((),filled) ∧
      LocalContent filled h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) next result (fun i => bfn ia (io+i)) 0 0 [] ∧
      StreamAccounting offered next 65536 0 ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before=
        (do let bs ← deflate_slow (some (.tab (h.nextBlk+1))) Z_NO_FLUSH
            publicStrategyReturn (some (.tab h.nextBlk)) (some (.tab (h.nextBlk+1))) Z_NO_FLUSH bs) filled ∧
      WindowLoopReached filled (.tab h.nextBlk) h.nextBlk (h.nextBlk+1) 0 0 next result (fun i => bfn ia (io+i)) [] := by
  have nonzero : ai≠0 := by intro zero;rw [zero] at large;change 65536<0 at large;omega
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  obtain ⟨header,z,d,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,
      _source,_input,_out,_zero,getInput⟩ :=
    fresh_header_source_ready (io := io) (n := ai) fresh globals allocations writableTwo inputBytes separate
  let r := ZStreamRef.tab h.nextBlk
  let ds := h.nextBlk+1
  let offered := {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := ai}
  let before := r.put header offered
  obtain ⟨setup,stateR,chainsR,fieldsR,controlsR,symbolsR,_frame⟩ :=
    local_data_rebuffer state chains fields controls symbols (.ref (.blk ob) (oo+2)) (.ref (.blk ib) io) 1 ai
  obtain ⟨w,p,q,b,blocks⟩ := stateR.inv.blocks
  obtain ⟨wa,getWindow,size⟩ := blocks.wa
  have wid : w=h.nextBlk+2 := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans controlsR.2.2.2.2.2.1)).1
  subst w
  have size : wa.size=65536 := by rw [fieldsR.2.2.2.2.1] at size;exact size
  let recordedD := {d with last_flush := Z_NO_FLUSH}
  let recorded := setD before ds recordedD
  have state0 := local_last_flush stateR Z_NO_FLUSH
  have chains0 : HeapChains recorded recordedD 0 := by
    obtain ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩ := chainsR
    exact ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩
  have symbols0 : SymbolBoundary recorded ds recordedD [] := by
    obtain ⟨pb,buf,trees,ledger,balance⟩ := symbolsR
    exact local_symbol_boundary_of_ledger state0 trees.base.pbuf trees.base.bytes (ledger.keep rfl rfl rfl rfl) balance
  have sourceInput : Space.get recorded (BRef.blk ib)=some ia := by
    change recorded.bytes ib=some ia
    simpa only [recorded,before,setD_bytes,ZStreamRef.put_bytes] using getInput
  have oldInput : ib<h.nextBlk := fresh.lt (by simp [Heap.live,inputBytes])
  have different : BRef.blk (h.nextBlk+2)≠BRef.blk ib := by intro same;cases same;omega
  have nEqual : rbLen ai 65536=65536 := UInt32.toNat_inj.mp (by
    have count := rbLen_nat ai 65536
    change (rbLen ai 65536).toNat=min ai.toNat 65536 at count
    change (rbLen ai 65536).toNat=65536
    omega)
  obtain ⟨fill,content,account⟩ := first_fill_local_content state0 fieldsR chains0 symbols0
    controlsR.2.2.2.2.1 controlsR.2.2.2.1 controlsR.2.2.2.2.2.1 getWindow blocks.wro size rfl
    sourceInput (by change io+ai.toNat≤ia.size;exact sourceBound) nonzero (Or.inl different)
  simp only [nEqual] at content account
  let copied := copyRange wa ia 0 io 65536
  let result := firstFillState recordedD 65536 copied
  let filled := firstFillHeap recorded r ds (h.nextBlk+2) offered recordedD (.blk ib) io ia wa
  let next := readStream offered 65536 (.blk ib) io (adlerValue offered.adler ((ia.toList.drop io).take 65536))
  change LocalContent filled h.nextBlk r ds next result (fun i => bfn ia (io+i)) 0 0 [] at content
  have scalar : result.strstart=0 ∧ result.lookahead=65536 ∧ result.w_size=32768 ∧ result.wrap=1 := by
    unfold result firstFillState primeState
    split <;> exact ⟨fieldsR.1,rfl,fieldsR.2.2.2.2.1,fieldsR.2.2.2.2.2.2.1⟩
  have endpoint : fillEnd result=65536 := by
    change result.strstart.toNat+result.lookahead.toNat=65536
    rw [scalar.1,scalar.2.1]
    rfl
  have inputAfter : filled.bytes ib=some ia := by
    simpa only [filled,firstFillHeap,recorded,before,setD_bytes,ZStreamRef.put_bytes,
      upd_ne _ _ _ _ (show ib≠h.nextBlk+2 from by omega)] using getInput
  have roots : result.window=.ref (.blk (h.nextBlk+2)) 0 ∧ result.prev=.ref (.blk (h.nextBlk+3)) 0 ∧
      result.head=.ref (.blk (h.nextBlk+4)) 0 ∧ result.pending_buf=.ref (.blk (h.nextBlk+5)) 0 := by
    unfold result firstFillState primeState recordedD
    split <;> exact ⟨controlsR.2.2.2.2.2.1,controlsR.2.2.2.2.2.2.1,controlsR.2.2.2.2.2.2.2.1,controlsR.2.2.2.2.2.2.2.2⟩
  have outside : ¬DeflateOwned ds result ib := by
    intro bad
    simp only [DeflateOwned,roots.1,roots.2.1,roots.2.2.1,roots.2.2.2,Ptr.ref.injEq,
      BRef.blk.injEq,WRef.blk.injEq,and_true] at bad
    dsimp only [ds] at bad
    omega
  have remaining : next.avail_in≠0 := by
    intro zero
    have value : next.avail_in.toNat=ai.toNat-65536 := by
      change (ai-65536).toNat=ai.toNat-65536
      exact UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le];change 65536≤ai.toNat;omega)
    rw [zero] at value
    change 0=ai.toNat-65536 at value
    omega
  have checkpoint : WindowLoopReached filled r h.nextBlk ds 0 0 next result (fun i => bfn ia (io+i)) [] :=
    local_window_loop_slide_checkpoint content (by change (1 : UInt32)≠0;decide) scalar.1 scalar.2.2.1 endpoint
      scalar.2.2.2 (ib := ib) (io := io+65536) rfl inputAfter
      (by change io+65536+(ai-65536).toNat≤ia.size
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le];change 65536≤ai.toNat;omega)]
          change io+65536+(ai.toNat-65536)≤ia.size
          omega) remaining outside (by intro j hj;simp only [Nat.zero_add,endpoint];congr 1;omega) Z_NO_FLUSH
  have offeredRun : splitHeaderOffer r ob oo (.ref (.blk ib) io) ai
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok ((),before) := by
    simp only [C.run] at setup
    change splitHeaderPrefix r (.ref (.blk ob) oo) (.ref (.blk ib) io) ai
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok (Z_OK,header) at prefixRun
    change zwr (some r) (fun z => {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := ai}) header=.ok ((),before) at setup
    simp only [splitHeaderOffer,bind_app,prefixRun,setup]
  have recordRun : C.run (wr (some (.tab ds)) (fun d => {d with last_flush := Z_NO_FLUSH})) before=.ok ((),recorded) := by
    change wr (some (.tab ds)) (fun d => {d with last_flush := Z_NO_FLUSH}) before=_
    rw [wrD_eq,stateR.live.hs]
  have entry := local_busy_valid_nonempty_entry stateR.live busy pending
    (by intro bad;cases bad) (by change (1 : UInt32)≠0;decide) (by intro _ bad;cases bad)
    (by rw [last];decide) (by rw [last];decide) nonzero Z_NO_FLUSH (by decide) (by decide)
  have dispatch := public_busy_no_flush_slow_source state0.live.hz state0.live.hs busy
    fieldsR.2.2.2.2.2.2.2.1 fieldsR.2.2.2.2.2.2.2.2 (Or.inl nonzero)
  have ready : ¬result.lookahead<MIN_LOOKAHEAD_u := by rw [scalar.2.1];decide
  have prepend : deflate_slow (some (.tab ds)) Z_NO_FLUSH recorded=deflate_slow (some (.tab ds)) Z_NO_FLUSH filled :=
    slow_call_prepend_fill state0.live.hs fieldsR.2.1 fill content.state.live.hs ready Z_NO_FLUSH
  refine ⟨before,recorded,filled,offered,next,result,offeredRun,stateR.live.hz,recordRun,fill,content,account,?_,checkpoint⟩
  rw [entry,dispatch,bind_app,bind_app,prepend]

end ZlibF.Spec.Public.Proofs.CompressLocalFreshWindowLoop
