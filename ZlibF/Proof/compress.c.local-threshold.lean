import ZlibF.Proof.«compress.c.local-hash»
import ZlibF.Proof.«compress.c.local-refill-empty»
import ZlibF.Proof.«deflate.c.engine.slow-threshold»

/-! # A complete actual threshold strategy call with local private state -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalThreshold
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalData ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Spec.Public.Proofs.CompressLocalRefillEmpty ZlibF.Spec.Public.Proofs.CompressLocalFill
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_slow_resume_short_body {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : LocalState h cutoff r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat)
    (short : d.lookahead < MIN_LOOKAHEAD_u) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h =
      .ok ({ st with ret := some need_more }, h) := by
  have fill := (local_fill_window_resume_no_input good input noSlide range padded).1
  rw [slow_body_source]
  simp only [bind_app, rdD_eq, good.live.hs, short, ite_true, fill, Z_NO_FLUSH,
    show ((0 : Int32) == 0) = true from rfl]
  rfl

set_option maxHeartbeats 1000000 in
/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
With exactly MIN_LOOKAHEAD bytes in the first window and no further input,
the real strategy searches, defers one byte, resumes fill_window and
returns need_more. This is a whole strategy call, including its loop.
The public wrapper and block-emission paths are separate obligations. -/
theorem local_slow_threshold_call {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat 0 (d.strstart.toNat + d.lookahead.toNat))
    (start : d.strstart = 0) (lookahead : d.lookahead = 262) (ws : d.w_size = 32768)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (length : d.match_length = 2) (available : d.match_available = 0)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 1 ∧
      result.strstart = 1 ∧ result.lookahead = 261 ∧ result.match_available = 1 ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have extent : wa.size = d.window_size.toNat := by
    obtain ⟨w0,p0,q0,b0,blocks⟩ := good.inv.blocks
    have wid : w0 = w := by simpa only [env.win,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.win.symm
    subst w0
    obtain ⟨a,get,size⟩ := blocks.wa
    have same : a = wa := Option.some.inj (get.symm.trans env.wbytes)
    rw [good.inv.wsz]
    rwa [same] at size
  obtain ⟨key,after,first,goodA,chainsA,ss,la,_,exactHeap⟩ :=
    local_first_defer good env chains (by simp [start]) (by simp [start])
      (by rw [lookahead]; decide) (by omega) range form length available Z_NO_FLUSH {}
  let result := deferOne (lazyPrepare {d with ins_h := key})
  let st : LoopS := {hash_head := 0,bflush := false}
  have rangeA : result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat := by
    change result.strstart.toNat+result.lookahead.toNat ≤ d.window_size.toNat
    change result.strstart.toNat = d.strstart.toNat+1 at ss
    change result.lookahead.toNat = d.lookahead.toNat-1 at la
    rw [ss,la]
    have pos : 1 ≤ d.lookahead.toNat := by rw [lookahead]; decide
    omega
  have ssA : result.strstart = 1 := by
    apply UInt32.toNat_inj.mp
    exact ss.trans (by rw [start]; rfl)
  have laA : result.lookahead = 261 := by
    apply UInt32.toNat_inj.mp
    exact la.trans (by rw [lookahead]; rfl)
  have noSlide : ¬ result.strstart ≥ result.w_size + (result.w_size - MIN_LOOKAHEAD_u) := by
    change ¬ result.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    rw [ssA, ws]
    decide
  have paddedA : min (result.strstart.toNat + result.lookahead.toNat + 258)
      result.window_size.toNat ≤ result.high_water.toNat := by
    change min (result.strstart.toNat + result.lookahead.toNat + 258)
      d.window_size.toNat ≤ d.high_water.toNat
    have endpoint : result.strstart.toNat + result.lookahead.toNat =
        d.strstart.toNat + d.lookahead.toNat := by
      rw [ssA, laA, start, lookahead]
      rfl
    rw [endpoint]
    exact padded
  have second := local_slow_resume_short_body goodA input noSlide rangeA paddedA
    (by rw [laA]; decide) st
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h =
      .ok ({ st with ret := some need_more }, after) := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
      (18446744073709551613 + 3) {} h = _
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
        (18446744073709551613 + 2) x) h = _
    rw [bind_app, first]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
        (18446744073709551613 + 1) x) after = _
    rw [bind_app, second]
    simp only []
    rw [cwhile.go]
    rfl
  have effects := local_defer_heap_effects good env key
  dsimp only at effects
  rw [←exactHeap] at effects
  refine ⟨after, result, ?_, goodA, ?_, ssA, laA, rfl,effects⟩
  · unfold deflate_slow
    rw [bind_app, loop]
    rfl
  · have top : d.strstart.toNat + 1 = 1 := by rw [start]; rfl
    rwa [top] at chainsA

theorem local_slow_first_threshold {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (count : z.avail_in = 262)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let z' := readStream z n ref io
      (ZlibF.Spec.Public.adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      LocalState after cutoff r ds z' result ∧ HeapChains after result 1 ∧
      result.strstart = 1 ∧ result.lookahead = 261 ∧ result.match_available = 1 ∧
      StreamAccounting z z' 262 0 ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let filled := firstFillHeap h r ds w z d ref io ia wa
  let df := firstFillState d n copied
  have nonzero : z.avail_in ≠ 0 := by rw [count]; decide
  have nval : n = 262 := by change rbLen z.avail_in 65536 = 262; rw [count]; decide
  obtain ⟨fill,goodF,account,frame,shape,lookF,startF,_⟩ :=
    local_fill_window_first good win get writable size ss la ins hw ws wsz wrap
      pointer input inputBound nonzero separate
  have chainsF := first_fill_chains (r := r) (ds := ds) (z := z) (ref := ref) (io := io) (ia := ia) chains win get ss la
  have rangeF : df.strstart.toNat+df.lookahead.toNat ≤ df.window_size.toNat := by
    change (firstFillState d n copied).strstart.toNat+(firstFillState d n copied).lookahead.toNat ≤
      (firstFillState d n copied).window_size.toNat
    have keep := firstFillState_keep d n copied
    rw [keep.2.2.2.1,keep.2.2.2.2,ss,nval]
    change 0+262 ≤ d.window_size.toNat
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
  have look : df.lookahead = 262 := keep.2.1.trans nval
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
  obtain ⟨after, result, run, goodA, chainsA, startA, lookA, availA,shapeA,frameA,liveA,allocA,nextA⟩ :=
    local_slow_threshold_call goodF env H start look (keep.2.2.1.trans ws) rangeF padding inputF
      (keep.2.2.2.2.2.1.trans length) (keep.2.2.2.2.2.2.trans available) form
  have frameF : Frame h filled (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken frame
    intro b member
    rcases member with root | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst b; exact Or.inr (Or.inr (Or.inl win))
  have frameA' : Frame filled after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken frameA
    intro b member
    rcases member with root | owned
    · exact Or.inl root
    · right
      unfold DeflateOwned at owned ⊢
      unfold firstFillState primeState at owned
      split at owned <;> exact owned
  have frameFull := full_frame_trans_shape frameF frameA' shape
  have shapeFull := shape.trans shapeA
  have exactAccount : StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) 262 0 := by
    have actualAccount := account
    change StreamAccounting z (readStream z n ref io
      (adlerValue z.adler ((ia.toList.drop io).take n.toNat))) n.toNat 0 at actualAccount
    simpa only [nval,show (262 : UInt32).toNat = 262 from by decide +kernel] using actualAccount
  refine ⟨after, result, ?_, goodA, chainsA, startA, lookA, availA,exactAccount,
    shapeFull,frameFull,full_shape_live_change shapeFull,?_,?_⟩
  · rw [slow_call_prepend_fill good.live.hs la fill goodF.live.hs
      (by rw [look]; decide) Z_NO_FLUSH]
    exact run
  · simpa [firstFillHeap] using allocA
  · simpa [firstFillHeap] using nextA

/-- A complete actual public NO_FLUSH request with a first 262-byte offer.
The actual entry, first refill, hash insertion, deferred decision, resumed
empty refill, loop exit and public return all concern one execution.
Output may be any nonnull byte pointer: this branch writes no caller output.
-/
theorem local_threshold_no_flush {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (fields : InitialReadFields d)
    (chains : HeapChains h d 0) (busy : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (rw : h.ro w = false) (size : wa.size = 65536)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (bound : io+z.avail_in.toNat ≤ ia.size) (count : z.avail_in = 262)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io+(rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK,after) ∧
      LocalState after cutoff r ds z' result ∧ HeapChains after result 1 ∧
      StreamAccounting z z' 262 0 ∧ z'.avail_in = 0 ∧
      result.strstart = 1 ∧ result.lookahead = 261 ∧ result.match_available = 1 ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
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
  obtain ⟨after,result,slow,stateA,chainsA,ss,la,avail,account,shape,frame,live,alloc,next⟩ :=
    local_slow_first_threshold state0 chains0 win get rw size fields.1 fields.2.1 fields.2.2.1
      fields.2.2.2.1 fields.2.2.2.2.1 fields.2.2.2.2.2.1 fields.2.2.2.2.2.2.1
      length available pointer (by simpa only [byte_view_setD_depth state.live.hs (show ({d with last_flush := Z_NO_FLUSH} : DeflateState).depth = d.depth from rfl) ref] using input) bound count separate
  have dispatch := public_busy_no_flush_slow_source state0.live.hz state0.live.hs busy
    fields.2.2.2.2.2.2.2.1 fields.2.2.2.2.2.2.2.2 (Or.inl nonzero)
  have returned := public_need_more_return stateA.live.hz stateA.live.hs Z_NO_FLUSH
  have outputSame : (readStream z (rbLen z.avail_in 65536) ref io
      (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat))).avail_out = z.avail_out := rfl
  have offer : rbLen z.avail_in 65536 = 262 := by rw [count]; decide
  have allInput : (readStream z (rbLen z.avail_in 65536) ref io
      (adlerValue z.adler ((ia.toList.drop io).take (rbLen z.avail_in 65536).toNat))).avail_in = 0 := by
    change z.avail_in-rbLen z.avail_in 65536 = 0
    rw [offer,count]; decide
  have frame0 : Frame h before (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds recorded) (fun _ same => Or.inr (Or.inl same))
  have shape0 := shape_setD state.live.hs recorded
  have fullFrame := full_frame_trans_shape frame0 frame shape0
  have fullShape := shape0.trans shape
  refine ⟨after,result,?_,stateA,chainsA,account,allInput,ss,la,avail,fullShape,fullFrame,
    full_shape_live_change fullShape,alloc,next⟩
  rw [entry,dispatch]
  simp only [bind_app,slow,returned,outputSame,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    Bool.false_eq_true,ite_false]

end ZlibF.Spec.Public.Proofs.CompressLocalThreshold
