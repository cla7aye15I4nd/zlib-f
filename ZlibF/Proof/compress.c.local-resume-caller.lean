import ZlibF.Proof.«compress.c.local-resume-content»
import ZlibF.Proof.«compress.c.local-fresh-content»

/-! # Actual stream offers and continuation through resumed content -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalResumeCaller
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalResumeContent
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalData ZlibF.Spec.Public.Proofs.CompressLocalDataHistory
open ZlibF.Spec.Public.Proofs.CompressLocalPendingData ZlibF.Spec.Public.Proofs.CompressLocalSymbols
open ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Spec.Public.Proofs.CompressLocalRefill
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual legal four-field stream rebuffer leaves content and all
private typed objects intact, even with old caller typed-key collisions. -/
theorem local_content_rebuffer {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (dest source : BPtr) (ao ai : UInt32) :
    let next := {z with next_out := dest,avail_out := ao,next_in := source,avail_in := ai}
    let after := r.put h next
    C.run (zwr (some r) (fun z => {z with next_out := dest,avail_out := ao,next_in := source,avail_in := ai})) h = .ok ((),after) ∧
      LocalContent after cutoff r ds next d input origin base xs ∧ Frame h after (StreamRoot r) := by
  let next := {z with next_out := dest,avail_out := ao,next_in := source,avail_in := ai}
  have stateA := local_state_setZD boundary.state (z' := next) (d' := d) rfl
    boundary.state.live.zalloc boundary.state.live.zfree rfl boundary.state.live.status boundary.state.inv (by trkeep)
  have getD : (r.put h next).dstates ds = some d := by simpa using boundary.state.live.hs
  rw [setD_self getD] at stateA
  have chainsKeep : ∀ top, HeapChains h d top → HeapChains (r.put h next) d top := by
    intro top chains
    obtain ⟨w,p,q,wa,pa,qa,win,prev,head,bytes,wordsP,wordsQ,H⟩ := chains
    exact ⟨w,p,q,wa,pa,qa,win,prev,head,by simpa using bytes,by simpa using wordsP,by simpa using wordsQ,H⟩
  have symbols : SymbolBoundary (r.put h next) ds d xs := by
    obtain ⟨b,buf,trees,ledger,balance⟩ := boundary.symbols
    exact local_symbol_boundary_of_ledger stateA trees.base.pbuf (by simpa using trees.base.bytes) ledger balance
  have data : ∃ w wa, d.window = .ref (.blk w) 0 ∧ (r.put h next).bytes w=some wa ∧
      (∀ i, i<fillEnd d → bfn wa i=input (origin+i)) ∧
      (3≤d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) := by
    obtain ⟨w,wa,win,get,view,form⟩ := boundary.data
    exact ⟨w,wa,win,by simpa using get,view,form⟩
  exact ⟨by simp [C.run,zwr_eq,boundary.state.live.hz],
    ⟨stateA,chainsKeep _ boundary.chains,boundary.range,boundary.history,boundary.deferred,symbols,data,
      boundary.insert_le,chainsKeep _ boundary.frontier,boundary.ready,boundary.trace,boundary.accounted⟩,
    stream_store_full_frame h r next⟩

/-- The real slow loop with short buffered input first performs the real
refill. Once its result is ready, both calls have exactly the same body
and continuation, with the original loop fuel retained. -/
theorem slow_call_prepend_resume {h after : Heap} {ds : Nat} {d df : DeflateState}
    (state : h.dstates ds=some d) (short : d.lookahead < MIN_LOOKAHEAD_u)
    (fill : fill_window (some (.tab ds)) h=.ok ((),after))
    (result : after.dstates ds=some df) (ready : ¬df.lookahead<MIN_LOOKAHEAD_u)
    (flush : Int32) :
    deflate_slow (some (.tab ds)) flush h=deflate_slow (some (.tab ds)) flush after := by
  have body : deflate_slow_body (some (.tab ds)) flush {} h=
      deflate_slow_body (some (.tab ds)) flush {} after := by
    rw [slow_body_source]
    simp only [bind_app,rdD_eq,state,short,ite_true,fill,result,ready,ite_false,
      decide_false,Bool.false_and,Bool.false_eq_true,
      show ¬(df.lookahead==0)=true from by
        simp only [beq_iff_eq]
        intro zero
        apply ready
        rw [zero]
        decide]
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} after := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (18446744073709551615+1) {} h=
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (18446744073709551615+1) {} after
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) flush {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) 18446744073709551615 x) h=
      (deflate_slow_body (some (.tab ds)) flush {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) 18446744073709551615 x) after
    simp only [bind_app,body]
  unfold deflate_slow
  simp only [bind_app,loop]

/-- Parameterized two-offer branch of a real Fresh client history. The
first nonempty offer has at most 261 bytes and really returns OK. The
second offer resumes at the next byte of the same original source array.
All private conditions of the second refill are derived from that actual
returned state. The final clause anchors the ordinary caller continuation
when the resulting buffered input reaches the search threshold. This is
not a whole utility or arbitrary FINISH result. -/
theorem fresh_two_offer_content {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8} {a b : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j<5 → h.allocOk (h.nalloc+j)=true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib=some ia)
    (sourceBound : io+a.toNat+b.toNat≤ia.size) (firstNonzero : a≠0) (firstShort : a.toNat≤261)
    (secondNonzero : b≠0) (separate : ib≠ob) :
    ∃ before first ready filled offered returned second final d1 d2,
      splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) a
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok ((),before) ∧
      (ZStreamRef.tab h.nextBlk).get before=some offered ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before=.ok (Z_OK,first) ∧
      LocalContent first h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) returned d1
        (fun i => bfn ia (io+i)) 0 0 [] ∧
      StreamAccounting offered returned a.toNat 0 ∧ returned.avail_in=0 ∧
      C.run (zwr (some (.tab h.nextBlk)) (fun z => {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1, next_in := .ref (.blk ib) (io+a.toNat),avail_in := b})) first=.ok ((),ready) ∧
      (ZStreamRef.tab h.nextBlk).get ready=some second ∧
      fill_window (some (.tab (h.nextBlk+1))) ready=.ok ((),filled) ∧
      LocalContent filled h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) final d2
        (fun i => bfn ia (io+i)) 0 0 [] ∧
      StreamAccounting second final (min b.toNat (65536-a.toNat)) 0 ∧
      fillEnd d2=a.toNat+min b.toNat (65536-a.toNat) ∧
      (262≤d2.lookahead.toNat → deflate (some (.tab h.nextBlk)) Z_NO_FLUSH ready=
        (do let bs ← deflate_slow (some (.tab (h.nextBlk+1))) Z_NO_FLUSH
            publicStrategyReturn (some (.tab h.nextBlk)) (some (.tab (h.nextBlk+1))) Z_NO_FLUSH bs) filled) := by
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  obtain ⟨header,z,d,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,
      _source,_input,_out,_zero,getInput⟩ :=
    fresh_header_source_ready (io := io) (n := a) fresh globals allocations writableTwo inputBytes separate
  let ds := h.nextBlk+1
  let r := ZStreamRef.tab h.nextBlk
  let offered := {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := a}
  let before := r.put header offered
  obtain ⟨setup,stateR,chainsR,fieldsR,controlsR,symbolsR,_frame⟩ :=
    local_data_rebuffer state chains fields controls symbols (.ref (.blk ob) (oo+2)) (.ref (.blk ib) io) 1 a
  obtain ⟨w,p,q,pb,blocks⟩ := stateR.inv.blocks
  obtain ⟨wa,getWindow,size⟩ := blocks.wa
  have wid : w=h.nextBlk+2 := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans controlsR.2.2.2.2.2.1)).1
  subst w
  have size : wa.size=65536 := by rw [fieldsR.2.2.2.2.1] at size;exact size
  have oldInput : ib<h.nextBlk := fresh.lt (by simp [Heap.live,inputBytes])
  have different : BRef.blk (h.nextBlk+2)≠BRef.blk ib := by intro same;cases same;omega
  have sourceInput : Space.get before (BRef.blk ib)=some ia := by simpa [before,r] using getInput
  change before.bytes ib=some ia at sourceInput
  have nEqual : rbLen a 65536=a := UInt32.toNat_inj.mp (by
    have n := rbLen_nat a 65536
    change (rbLen a 65536).toNat=min a.toNat 65536 at n
    omega)
  let recordedD := {d with last_flush := Z_NO_FLUSH}
  let recorded := setD before ds recordedD
  let copied := copyRange wa ia 0 io a.toNat
  let d1 := firstFillState recordedD a copied
  let returned := readStream offered a (.blk ib) io (adlerValue offered.adler ((ia.toList.drop io).take a.toNat))
  let first := firstFillHeap recorded r ds (h.nextBlk+2) offered recordedD (.blk ib) io ia wa
  obtain ⟨firstRun,state1,account1,input0,look1,busy1,last1,_firstFrame,getFirst⟩ :=
    local_short_no_flush stateR fieldsR busy pending (by rw [last];decide) (by rw [last];decide)
      (by intro bad;cases bad) (by change (1 : UInt32) ≠ 0;decide) controlsR.2.2.2.2.2.1 getWindow blocks.wro size
      (ref := .blk ib) (io := io) (ia := ia) rfl sourceInput (by change io+a.toNat≤ia.size;omega) firstNonzero firstShort (Or.inl different)
  have state0 := local_last_flush stateR Z_NO_FLUSH
  have chains0 : HeapChains recorded recordedD 0 := by
    obtain ⟨wb,pp,qq,bytes,prev,head,wp,pptr,qptr,bw,bp,bq,H⟩ := chainsR
    exact ⟨wb,pp,qq,bytes,prev,head,wp,pptr,qptr,bw,bp,bq,H⟩
  have symbols0 : SymbolBoundary recorded ds recordedD [] := by
    obtain ⟨bb,buf,trees,ledger,balance⟩ := symbolsR
    exact local_symbol_boundary_of_ledger state0 trees.base.pbuf trees.base.bytes (ledger.keep rfl rfl rfl rfl) balance
  obtain ⟨_fill,content1,_account⟩ := first_fill_local_content state0 fieldsR chains0 symbols0
    controlsR.2.2.2.2.1 controlsR.2.2.2.1 controlsR.2.2.2.2.2.1 getWindow blocks.wro size
    (ref := .blk ib) (io := io) (ia := ia) rfl (by change recorded.bytes ib=some ia;simpa only [recorded,setD_bytes] using sourceInput)
    (by change io+a.toNat≤ia.size;omega) firstNonzero (Or.inl different)
  simp only [nEqual] at firstRun state1 account1 input0 look1 busy1 last1 getFirst content1
  change LocalContent first h.nextBlk r ds returned d1 (fun i => bfn ia (io+i)) 0 0 [] at content1
  have controls1 : d1.strstart=0 ∧ d1.insert=0 ∧ d1.w_size=32768 ∧ d1.window_size=65536 ∧
      d1.wrap=1 ∧ d1.level=6 ∧ d1.strategy=0 ∧ d1.pending=0 ∧ d1.last_flush=Z_NO_FLUSH := by
    unfold d1 firstFillState primeState recordedD
    split <;> exact ⟨fieldsR.1,fieldsR.2.2.1,fieldsR.2.2.2.2.1,fieldsR.2.2.2.2.2.1,
      fieldsR.2.2.2.2.2.2.1,fieldsR.2.2.2.2.2.2.2.1,fieldsR.2.2.2.2.2.2.2.2,pending,rfl⟩
  let second := {returned with next_out := .ref (.blk ob) (oo+2),avail_out := 1, next_in := .ref (.blk ib) (io+a.toNat),avail_in := b}
  let ready := r.put first second
  obtain ⟨rebuffer,contentR,_refillFrame⟩ := local_content_rebuffer content1
    (.ref (.blk ob) (oo+2)) (.ref (.blk ib) (io+a.toNat)) 1 b
  have inputR : Space.get ready (BRef.blk ib)=some ia := by
    change ready.bytes ib=some ia
    simpa only [ready,first,recorded,before,firstFillHeap,setD_bytes,ZStreamRef.put_bytes,
      upd_ne _ _ _ _ (show ib≠h.nextBlk+2 from by omega)] using getInput
  let oldWindow := fillRange copied a.toNat (firstPadding a).toNat 0
  have getReady : ready.bytes (h.nextBlk+2)=some oldWindow := by simpa [ready] using getFirst
  have window1 : d1.window=.ref (.blk (h.nextBlk+2)) 0 := by
    unfold d1 firstFillState primeState;split <;> exact controlsR.2.2.2.2.2.1
  have endpoint1 : fillEnd d1=a.toNat := by
    change d1.strstart.toNat+d1.lookahead.toNat=a.toNat
    rw [controls1.1,look1]
    exact Nat.zero_add _
  have noSlide : ¬d1.strstart≥d1.w_size+(d1.w_size-MIN_LOOKAHEAD_u) := by
    rw [controls1.1,controls1.2.2.1];decide
  obtain ⟨fill2,content2,account2,frame2,shape2,end2⟩ := local_resume_content contentR window1 getReady
    (by rw [look1];omega) noSlide controls1.2.1 controls1.2.2.2.2.1 rfl inputR sourceBound secondNonzero
    (Or.inl different) (by intro j hj;simp only [Nat.zero_add,endpoint1];congr 1;omega)
  have count2 := rbLen_nat b (fillMore d1)
  have more : (fillMore d1).toNat=65536-a.toNat := by
    have natural := local_fill_more_nat contentR.state window1 getReady contentR.range
    change (fillMore d1).toNat=d1.window_size.toNat-fillEnd d1 at natural
    rw [natural,controls1.2.2.2.1,endpoint1]
    rfl
  change (rbLen b (fillMore d1)).toNat=min b.toNat (fillMore d1).toNat at count2
  rw [more] at count2
  have offeredRun : splitHeaderOffer r ob oo (.ref (.blk ib) io) a
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok ((),before) := by
    simp only [C.run] at setup
    change splitHeaderPrefix r (.ref (.blk ob) oo) (.ref (.blk ib) io) a
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h)=.ok (Z_OK,header) at prefixRun
    change zwr (some r) (fun z => {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := a}) header=.ok ((),before) at setup
    unfold splitHeaderOffer
    simp only [bind_app,prefixRun,setup]
  refine ⟨before,first,ready,_,offered,returned,second,_,d1,_,offeredRun,stateR.live.hz,
    firstRun,content1,account1,input0,rebuffer,contentR.state.live.hz,fill2,content2,?_,?_,?_⟩
  · simpa only [count2] using account2
  · simpa only [endpoint1,count2] using end2
  · intro enough
    have entry := local_busy_valid_nonempty_entry contentR.state.live busy1 controls1.2.2.2.2.2.2.2.1
      (by intro bad;cases bad) (by change (1 : UInt32) ≠ 0;decide) (by intro _ bad;cases bad)
      (by rw [controls1.2.2.2.2.2.2.2.2];decide) (by rw [controls1.2.2.2.2.2.2.2.2];decide)
      secondNonzero Z_NO_FLUSH (by decide) (by decide)
    have unchanged : {d1 with last_flush := Z_NO_FLUSH}=d1 := by rw [←controls1.2.2.2.2.2.2.2.2]
    have self : setD ready ds {d1 with last_flush := Z_NO_FLUSH}=ready := by rw [unchanged,setD_self contentR.state.live.hs]
    rw [self] at entry
    have dispatch := public_busy_no_flush_slow_source contentR.state.live.hz contentR.state.live.hs busy1
      controls1.2.2.2.2.2.1 controls1.2.2.2.2.2.2.1 (Or.inl secondNonzero)
    have prepended := slow_call_prepend_resume contentR.state.live.hs
      (by rw [UInt32.lt_iff_toNat_lt,look1];change a.toNat<262;omega) fill2 content2.state.live.hs
      (by rw [UInt32.lt_iff_toNat_lt];exact Nat.not_lt.mpr enough) Z_NO_FLUSH
    rw [entry,dispatch,bind_app,bind_app,prepended]

end ZlibF.Spec.Public.Proofs.CompressLocalResumeCaller
