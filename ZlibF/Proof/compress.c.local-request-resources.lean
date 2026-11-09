import ZlibF.Proof.«compress.c.local-loop-resources»

/-! # Actual first refill and complete request resource effects -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalRequestResources
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop ZlibF.Spec.Public.Proofs.CompressLocalFill
open ZlibF.Spec.Public.Proofs.CompressLocalData ZlibF.Spec.Public.Proofs.CompressLocalThreshold
open ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Spec.Public.Proofs.CompressLocalBodyResources ZlibF.Spec.Public.Proofs.CompressLocalLoopResources
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Resource effects for the actual first refill followed by the complete
263-byte strategy call. These are internal entry facts, not caller premises
of the original utility goal. -/
theorem first_literal_resources {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
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
      after.bytes w = some packedWindow ∧
      result.window = d.window ∧ result.prev = d.prev ∧ result.head = d.head ∧
      result.pending_buf = d.pending_buf ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
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
  obtain ⟨after,result,run,stateA,chainsA,symbolsA,startA,lookA,getA,record,shapeA,frameA,_liveA,allocA,nextA⟩ :=
    slow_literal_call_resources goodF symbolsF env H start look (keep.2.2.1.trans ws) rangeF windowF padding inputF out
      (keep.2.2.2.2.2.1.trans length) (keep.2.2.2.2.2.2.trans available)
      (by unfold firstFillState primeState; split <;> exact space) form
  have exactAccount : StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) 263 0 := by
    have actualAccount := account
    change StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) n.toNat 0 at actualAccount
    simpa only [nval,show (263 : UInt32).toNat = 263 from by decide +kernel] using actualAccount
  have keysF : df.window = d.window ∧ df.prev = d.prev ∧ df.head = d.head ∧ df.pending_buf = d.pending_buf := by
    unfold df firstFillState primeState
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨winA,prevA,headA,pendingA⟩ := record_owned_keys record
  have frameF : Frame h filled (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := by
    apply full_frame_weaken frame
    intro x member
    rcases member with root | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst x
      exact Or.inr (Or.inr (Or.inl win))
  have frameA' : Frame filled after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := by
    apply full_frame_weaken frameA
    intro x member
    rcases member with root | owned
    · exact Or.inl root
    · right
      change DeflateOwned ds df x at owned
      unfold DeflateOwned at owned
      rw [keysF.1,keysF.2.1,keysF.2.2.1,keysF.2.2.2] at owned
      exact owned
  have shapeAll := shape.trans shapeA
  have frameAll := full_frame_trans_shape frameF frameA' shape
  have storage := local_first_fill_storage (ref := ref) (io := io) (ia := ia) good.live get
  have allocF : filled.nalloc = h.nalloc := storage.2.2.1
  have nextF : filled.nextBlk = h.nextBlk := storage.2.1
  refine ⟨after,result,?_,stateA,chainsA,?_,exactAccount,startA,lookA,?_,
    winA.trans keysF.1,prevA.trans keysF.2.1,headA.trans keysF.2.2.1,pendingA.trans keysF.2.2.2,
    shapeAll,frameAll,full_shape_live_change shapeAll,allocA.trans allocF,nextA.trans nextF⟩
  · rw [slow_call_prepend_fill good.live.hs la fill goodF.live.hs (by rw [look]; decide) Z_NO_FLUSH]
    exact run
  · simpa only [array] using symbolsA
  · simpa only [array] using getA

theorem literal_no_flush_resources {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
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
      result.strstart = 2 ∧ result.lookahead = 261 ∧
      result.window = d.window ∧ result.prev = d.prev ∧ result.head = d.head ∧
      result.pending_buf = d.pending_buf ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
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
  obtain ⟨after,result,slow,stateA,chainsA,symbolsA,account,ss,la,_bytes,kw,kp,kh,kb,shapeA,frameA,_liveA,allocA,nextA⟩ :=
    first_literal_resources state0 chains0 symbols0 space positive win get rw size fields.1 fields.2.1 fields.2.2.1
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
  have shape0 : Shape h before := shape_setD state.live.hs recorded
  have frame0 : Frame h before (fun x => StreamRoot r x ∨ DeflateOwned ds d x) :=
    full_frame_weaken (state_store_full_frame h ds recorded) (fun _ same => Or.inr (Or.inl same))
  have frameA' : Frame before after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := frameA
  have shapeAll := shape0.trans shapeA
  have frameAll := full_frame_trans_shape frame0 frameA' shape0
  refine ⟨after,result,?_,stateA,chainsA,symbolsA,account,allInput,ss,la,kw,kp,kh,kb,
    shapeAll,frameAll,full_shape_live_change shapeAll,allocA,nextA⟩
  rw [entry,dispatch]
  simp only [bind_app,slow,returned,outputSame,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    Bool.false_eq_true,ite_false]

end ZlibF.Spec.Public.Proofs.CompressLocalRequestResources
