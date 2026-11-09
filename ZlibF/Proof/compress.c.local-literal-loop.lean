import ZlibF.Proof.«compress.c.local-literal-body»

/-! # A complete actual local slow call that emits its first literal -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody ZlibF.Spec.Public.Proofs.CompressLocalThreshold
open ZlibF.Spec.Public.Proofs.CompressLocalFill
open ZlibF.Spec.Public.Proofs.CompressLocalData ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The real first fill writes the window while retaining the packed
symbol buffer, leaf frequencies and byte balance on the exact same heap. -/
theorem local_first_fill_symbols {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (before : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d [])
    (win : d.window = .ref (.blk w) 0)
    (afterState : LocalState (firstFillHeap h r ds w z d ref io ia wa) cutoff r ds
      (readStream z (rbLen z.avail_in 65536) ref io
        (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat)))
      (firstFillState d (rbLen z.avail_in 65536) (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat))) :
    SymbolBoundary (firstFillHeap h r ds w z d ref io ia wa) ds
      (firstFillState d (rbLen z.avail_in 65536) (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat)) [] := by
  obtain ⟨b,buf,trees,ledger,balance⟩ := symbol
  obtain ⟨w0,p0,q0,b0,blocks⟩ := before.inv.blocks
  have wid : w0 = w := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans win)).1
  have bid : b0 = b := BRef.blk.inj (Ptr.ref.inj (blocks.pbuf.symm.trans trees.base.pbuf)).1
  subst w0 b0
  let df := firstFillState d (rbLen z.avail_in 65536) (copyRange wa ia 0 io (rbLen z.avail_in 65536).toNat)
  have pending : df.pending_buf = .ref (.blk b) 0 := by
    unfold df firstFillState primeState
    split <;> exact trees.base.pbuf
  have get : (firstFillHeap h r ds w z d ref io ia wa).bytes b = some buf := by
    simpa [firstFillHeap,upd_ne _ _ _ _ blocks.wb.symm] using trees.base.bytes
  have ledgerF : SymbolLedger buf df [] := by
    unfold df firstFillState primeState
    split <;> exact ledger.keep rfl rfl rfl rfl
  have balanceF : BlockBalance df [] (deferredCredit df) := by
    unfold df firstFillState primeState
    split <;> exact balance
  exact ZlibF.Spec.Public.Proofs.CompressLocalLiteral.local_symbol_boundary_of_ledger
    afterState pending get ledgerF balanceF

/-- Two actual remaining source bodies after the first deferred byte.
Keeping this intermediate record abstract avoids duplicating nested tree
updates while composing the actual loop. -/
theorem local_literal_tail_bodies {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d [])
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (start : d.strstart = 1) (look : d.lookahead = 262)
    (ws : d.w_size = 32768) (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (out : z.avail_out ≠ 0) (length : d.match_length = 2)
    (available : d.match_available ≠ 0) (space : d.sym_next.toNat+3 < d.sym_end.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result,
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} h = .ok ({},after) ∧
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} after = .ok ({ret := some need_more},after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 2 ∧
      SymbolBoundary after ds result [⟨0,wa[0]!.toNat⟩] ∧
      result.strstart = 2 ∧ result.lookahead = 261 ∧ after.bytes w = some wa := by
  obtain ⟨key,after,body,stateA,chainsA,symbolA,ss,la,get,_strict⟩ :=
    local_nil_literal_body state symbol env chains ordered start (by rw [look]; decide)
      window range form length available space out Z_NO_FLUSH {}
  let result := advanceOne (literalState (lazyPrepare {d with ins_h := key}) wa[0]!)
  have lookA : result.lookahead = 261 := UInt32.toNat_inj.mp (la.trans (by rw [look]; rfl))
  have winA : result.window_size = d.window_size := rfl
  have highA : result.high_water = d.high_water := rfl
  have sizeA : result.w_size = d.w_size := rfl
  have endpoint : d.strstart.toNat+d.lookahead.toNat = 263 := by rw [start,look]; decide
  have rangeA : result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat := by
    rw [winA,ss,lookA]
    change 263 ≤ d.window_size.toNat
    omega
  have noSlide : ¬result.strstart ≥ result.w_size+(result.w_size-MIN_LOOKAHEAD_u) := by
    rw [ss,sizeA,ws]; decide
  have paddingA : min (result.strstart.toNat+result.lookahead.toNat+258) result.window_size.toNat ≤ result.high_water.toNat := by
    rw [ss,lookA,winA,highA]
    change min 521 d.window_size.toNat ≤ d.high_water.toNat
    simpa only [endpoint] using padded
  have resumed := local_slow_resume_short_body stateA input noSlide rangeA paddingA (by rw [lookA]; decide) ({} : LoopS)
  exact ⟨after,result,body,resumed,stateA,chainsA,by simpa only [List.nil_append] using symbolA,ss,lookA,get⟩

/-- The complete actual 263-byte buffered strategy call performs two
insertions, defers one byte, publishes one literal symbol, resumes its
empty-input refill and returns need_more. Its symbol ledger is retained
on that same returned execution; source input bytes remain arbitrary. -/
theorem local_slow_literal_call {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d [])
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat 0 (d.strstart.toNat+d.lookahead.toNat))
    (start : d.strstart = 0) (look : d.lookahead = 263) (ws : d.w_size = 32768)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (out : z.avail_out ≠ 0)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (space : d.sym_next.toNat+3 < d.sym_end.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more,after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 2 ∧
      SymbolBoundary after ds result [⟨0,wa[0]!.toNat⟩] ∧
      result.strstart = 2 ∧ result.lookahead = 261 ∧ after.bytes w = some wa := by
  obtain ⟨key1,after1,first,state1,chains1,ss1,la1,form1,exact1⟩ :=
    local_first_defer state env chains (by simp [start]) (by simp [start])
      (by rw [look]; decide) window range form length available Z_NO_FLUSH {}
  let d1 := deferOne (lazyPrepare {d with ins_h := key1})
  have symbol1 := local_first_defer_symbols state1 symbol available ss1 exact1
  have start1 : d1.strstart = 1 := UInt32.toNat_inj.mp (ss1.trans (by rw [start]; rfl))
  have look1 : d1.lookahead = 262 := UInt32.toNat_inj.mp (la1.trans (by rw [look]; rfl))
  have get1 : after1.bytes w = some wa := by simpa [exact1,insertedHeap] using env.wbytes
  obtain ⟨wb,pb,qb,bytes,prev,head,env1,H1⟩ := local_heap_chains_environment state1 chains1
  have wid : wb = w := BRef.blk.inj (Ptr.ref.inj (env1.win.symm.trans env.win)).1
  subst wb
  have array : bytes = wa := Option.some.inj (env1.wbytes.symm.trans get1)
  subst bytes
  have range1 : d1.strstart.toNat+d1.lookahead.toNat ≤ d1.window_size.toNat := by
    change d1.strstart.toNat+d1.lookahead.toNat ≤ d.window_size.toNat
    rw [start1,look1]
    change 263 ≤ d.window_size.toNat
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 263 := by rw [start,look]; decide
    omega
  have window1 : d1.strstart.toNat+d1.lookahead.toNat ≤ wa.size := by
    rw [start1,look1]
    change 263 ≤ wa.size
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 263 := by rw [start,look]; decide
    omega
  have rolling : InsHForm d1.hash_shift d1.hash_mask (bfn wa) d1.strstart.toNat d1.ins_h := by
    change InsHForm d.hash_shift d.hash_mask (bfn wa) d1.strstart.toNat key1
    rw [ss1]
    exact form1
  have ordered : d.strstart.toNat+1 ≤ d1.strstart.toNat := by
    rw [ss1]
    exact Nat.le_refl _
  have padding1 : min (d1.strstart.toNat+d1.lookahead.toNat+258) d1.window_size.toNat ≤ d1.high_water.toNat := by
    change min (d1.strstart.toNat+d1.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat
    rw [start1,look1]
    change min 521 d.window_size.toNat ≤ d.high_water.toNat
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 263 := by rw [start,look]; decide
    simpa only [endpoint] using padded
  obtain ⟨after2,result,second,third,state2,chains2,symbol2,ss2,look2,get2⟩ :=
    local_literal_tail_bodies (d := d1) state1 symbol1 env1 H1 ordered start1 look1 ws range1 window1 padding1
      input out (by rfl) (by change (1 : Int32) ≠ 0; decide) space rolling
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h =
      .ok ({ret := some need_more},after2) := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551612+4) {} h = _
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551612+3) x) h = _
    rw [bind_app,first]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551612+2) x) after1 = _
    rw [bind_app,second]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551612+1) x) after2 = _
    rw [bind_app,third]
    simp only []
    rw [cwhile.go]
    rfl
  refine ⟨after2,result,?_,state2,chains2,?_,ss2,look2,get2⟩
  · unfold deflate_slow
    rw [bind_app,loop]
    rfl
  · exact symbol2

/-- The actual first caller-buffer read feeds the complete literal-producing
strategy call and retains exact source consumption on its returned heap. -/
theorem local_slow_first_literal {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d 0)
    (symbol : SymbolBoundary h ds d []) (space : d.sym_next.toNat+3 < d.sym_end.toNat) (out : z.avail_out ≠ 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (count : z.avail_in = 263)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let z' := readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let packedWindow := fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more,after) ∧
      LocalState after cutoff r ds z' result ∧ HeapChains after result 2 ∧
      SymbolBoundary after ds result [⟨0,packedWindow[0]!.toNat⟩] ∧
      StreamAccounting z z' 263 0 ∧ result.strstart = 2 ∧ result.lookahead = 261 ∧
      after.bytes w = some packedWindow := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let filled := firstFillHeap h r ds w z d ref io ia wa
  let df := firstFillState d n copied
  have nonzero : z.avail_in ≠ 0 := by rw [count]; decide
  have nval : n = 263 := by change rbLen z.avail_in 65536 = 263; rw [count]; decide
  obtain ⟨fill,goodF,account,frame,shape,lookF,startF,_⟩ :=
    local_fill_window_first good win get writable size ss la ins hw ws wsz wrap
      pointer input inputBound nonzero separate
  have chainsF := first_fill_chains (r := r) (ds := ds) (z := z) (ref := ref) (io := io) (ia := ia) chains win get ss la
  have rangeF : df.strstart.toNat+df.lookahead.toNat ≤ df.window_size.toNat := by
    change (firstFillState d n copied).strstart.toNat+(firstFillState d n copied).lookahead.toNat ≤
      (firstFillState d n copied).window_size.toNat
    have keep := firstFillState_keep d n copied
    rw [keep.2.2.2.1,keep.2.2.2.2,ss,nval]
    change 0+263 ≤ d.window_size.toNat
    rw [wsz]; decide
  have formF : n ≥ 3 → InsHForm d.hash_shift d.hash_mask (bfn padded) 0 df.ins_h := by
    intro enough
    exact first_fill_form (hash_parameters good.inv) (by rw [nval]; decide)
      (by rw [size_copyRange]; exact size) enough
  have keep : df.strstart = d.strstart ∧ df.lookahead = n ∧ df.w_size = d.w_size ∧
      df.window_size = d.window_size ∧ df.window = d.window ∧
      df.match_length = d.match_length ∧ df.match_available = d.match_available := by
    unfold df firstFillState primeState
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨wb, pb, qb, bytes, prev, head, env, H⟩ := local_heap_chains_environment goodF chainsF
  have wid : wb = w := by
    have eq := env.win.symm.trans (keep.2.2.2.2.1.trans win)
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using eq
  subst wb
  have array : bytes = padded := by
    have actual : filled.bytes w = some padded := by
      simp [filled, firstFillHeap, padded, copied, n]
    exact Option.some.inj (env.wbytes.symm.trans actual)
  have start : df.strstart = 0 := keep.1.trans ss
  have look : df.lookahead = 263 := keep.2.1.trans nval
  have form : InsHForm df.hash_shift df.hash_mask (bfn bytes) df.strstart.toNat df.ins_h := by
    have hashes : df.hash_shift = d.hash_shift ∧ df.hash_mask = d.hash_mask := by
      unfold df firstFillState primeState
      split <;> exact ⟨rfl,rfl⟩
    rw [array,start,hashes.1,hashes.2]
    change InsHForm d.hash_shift d.hash_mask (bfn padded) 0 df.ins_h
    exact formF (by change n ≥ 3; rw [nval]; decide)
  have padding : min (df.strstart.toNat + df.lookahead.toNat + 258)
      df.window_size.toNat ≤ df.high_water.toNat :=
    first_fill_padding ss wsz (by rw [nval]; decide)
  have inputF : (readStream z n ref io
      (ZlibF.Spec.Public.adlerValue z.adler ((ia.toList.drop io).take n.toNat))).avail_in = 0 := by
    change z.avail_in - n = 0
    rw [count, nval]
    decide
  have symbolsF := local_first_fill_symbols good symbol win goodF
  have windowF : df.strstart.toNat+df.lookahead.toNat ≤ bytes.size := by
    rw [array,start,look]
    rw [size_fillRange,size_copyRange,size]
    decide
  obtain ⟨after,result,run,stateA,chainsA,symbolsA,startA,lookA,getA⟩ :=
    local_slow_literal_call goodF symbolsF env H start look (keep.2.2.1.trans ws) rangeF windowF padding inputF out
      (keep.2.2.2.2.2.1.trans length) (keep.2.2.2.2.2.2.trans available)
      (by unfold firstFillState primeState; split <;> exact space) form
  have exactAccount : StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) 263 0 := by
    have actualAccount := account
    change StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) n.toNat 0 at actualAccount
    simpa only [nval,show (263 : UInt32).toNat = 263 from by decide +kernel] using actualAccount
  refine ⟨after,result,?_,stateA,chainsA,?_,exactAccount,startA,lookA,?_⟩
  · rw [slow_call_prepend_fill good.live.hs la fill goodF.live.hs (by rw [look]; decide) Z_NO_FLUSH]
    exact run
  · simpa only [array] using symbolsA
  · simpa only [array] using getA


/-- The first actual literal is the caller's first offered source byte;
window padding is beyond the copied range and cannot change that byte. -/
theorem first_fill_literal_byte {wa ia : Array UInt8} {io : Nat} {n : UInt32}
    (size : wa.size = 65536) (positive : 0 < n.toNat) (bound : n.toNat ≤ 65536) :
    (fillRange (copyRange wa ia 0 io n.toNat) n.toNat (firstPadding n).toNat 0)[0]! = ia[io]! := by
  have pad := firstPadding_nat n bound
  have fit : n.toNat+(firstPadding n).toNat ≤ (copyRange wa ia 0 io n.toNat).size := by
    rw [size_copyRange,size]
    omega
  have outside : ¬(n.toNat ≤ 0 ∧ 0 < n.toNat+(firstPadding n).toNat) := by omega
  rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,
    getElem?_fillRange _ _ _ _ _ fit,if_neg outside,
    getElem?_copyRange wa ia 0 io n.toNat 0 (by rw [size];omega)]
  simp [positive]

/-- The complete actual public first-263-byte NO_FLUSH request consumes
all offered bytes and stores a literal equal to the caller first byte.
The actual initial local state and symbols are internal history facts. -/
theorem local_literal_no_flush {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (fields : InitialReadFields d)
    (chains : HeapChains h d 0) (symbol : SymbolBoundary h ds d [])
    (space : d.sym_next.toNat+3 < d.sym_end.toNat) (busy : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (rw : h.ro w = false) (size : wa.size = 65536)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (bound : io+z.avail_in.toNat ≤ ia.size) (count : z.avail_in = 263)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK,after) ∧
      LocalState after cutoff r ds z' result ∧ HeapChains after result 2 ∧
      SymbolBoundary after ds result [⟨0,ia[io]!.toNat⟩] ∧
      StreamAccounting z z' 263 0 ∧ z'.avail_in = 0 ∧
      result.strstart = 2 ∧ result.lookahead = 261 := by
  have nonzero : z.avail_in ≠ 0 := by rw [count]; decide
  have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := by intro _; rw [pointer]; intro bad; cases bad
  have entry := local_busy_valid_nonempty_entry state.live busy pending out positive valid lower upper nonzero
    Z_NO_FLUSH (by decide) (by decide)
  let recorded := {d with last_flush := Z_NO_FLUSH}
  let before := setD h ds recorded
  have state0 := local_last_flush state Z_NO_FLUSH
  have chains0 : HeapChains before recorded 0 := by
    obtain ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩ := chains
    exact ⟨wb,pb,qb,bytes,prev,head,wp,pp,qp,gw,gp,gq,H⟩
  have symbols0 : SymbolBoundary before ds recorded [] := by
    obtain ⟨b,buf,trees,ledger,balance⟩ := symbol
    exact ZlibF.Spec.Public.Proofs.CompressLocalLiteral.local_symbol_boundary_of_ledger state0 trees.base.pbuf
      trees.base.bytes (ledger.keep rfl rfl rfl rfl) balance
  obtain ⟨after,result,slow,stateA,chainsA,symbolsA,account,ss,la,_bytes⟩ :=
    local_slow_first_literal state0 chains0 symbols0 space positive win get rw size fields.1 fields.2.1 fields.2.2.1
      fields.2.2.2.1 fields.2.2.2.2.1 fields.2.2.2.2.2.1 fields.2.2.2.2.2.2.1
      length available pointer
      (by simpa only [byte_view_setD_depth state.live.hs (show ({d with last_flush := Z_NO_FLUSH} : DeflateState).depth = d.depth from rfl) ref] using input)
      bound count separate
  have dispatch := public_busy_no_flush_slow_source state0.live.hz state0.live.hs busy
    fields.2.2.2.2.2.2.2.1 fields.2.2.2.2.2.2.2.2 (Or.inl nonzero)
  have returned := public_need_more_return stateA.live.hz stateA.live.hs Z_NO_FLUSH
  have outputSame : (readStream z (rbLen z.avail_in 65536) ref io
      (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat))).avail_out = z.avail_out := rfl
  have offer : rbLen z.avail_in 65536 = 263 := by rw [count]; decide
  have allInput : (readStream z (rbLen z.avail_in 65536) ref io
      (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat))).avail_in = 0 := by
    change z.avail_in-rbLen z.avail_in 65536 = 0
    rw [offer,count]; decide
  have byte := first_fill_literal_byte (ia := ia) (io := io) (n := rbLen z.avail_in 65536) size
    (by rw [offer]; decide) (by rw [offer]; decide)
  rw [byte] at symbolsA
  refine ⟨after,result,?_,stateA,chainsA,symbolsA,account,allInput,ss,la⟩
  rw [entry,dispatch]
  simp only [bind_app,slow,returned,outputSame,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    Bool.false_eq_true,ite_false]

end ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop
