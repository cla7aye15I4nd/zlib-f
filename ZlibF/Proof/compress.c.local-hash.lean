import ZlibF.Proof.«compress.c.local-data-entry»
import ZlibF.Proof.«deflate.c.engine.slow-defer»
import ZlibF.Proof.«deflate.c.engine.insert-full-storage»

/-! # Actual insertion and first lazy decision with locally unique private objects

Old caller objects may occupy multiple typed tables at one numeric owner.
Only the private allocation range is locally unique. The actual insertion
and slow strategy body retain their original source order.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalHash
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalHeader
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_words_set {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) (x : Nat) (a a0 : Array UInt16)
    (get : h.words x = some a0) (size : a.size = a0.size) :
    LocalState {h with words := upd h.words x (some a)} cutoff r ds z d := by
  have shape := shape_setW get a
  refine ⟨⟨?_,state.live.hs,state.live.zst,state.live.back,state.live.status,state.live.zalloc,state.live.zfree⟩,
    state.inv.words_set x a a0 get size,state.newUnique.shape shape,
    shape.fresh rfl state.fresh,TreesInv.words_set state.trees x a⟩
  cases r <;> simpa [ZStreamRef.get] using state.live.hz

theorem local_state_setD {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d d' : DeflateState}
    (state : LocalState h cutoff r ds z d) (back : d'.strm = d.strm)
    (status : GoodStatus d'.status) (inv : DStInv h ds d') (keep : TrKeep d d') :
    LocalState (setD h ds d') cutoff r ds z d' := by
  have next := local_state_setZD state (d' := d') rfl state.live.zalloc state.live.zfree back status inv keep
  rwa [ZStreamRef.put_self state.live.hz] at next

theorem local_heap_chains_environment {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : LocalState h cutoff r ds z d) (chains : HeapChains h d top) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa ∧
      HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
        d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat) := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by
    simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  have qe : q0 = q := by
    simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  subst w0 p0 q0
  have hsize : d.hash_size.toNat ≤ qa.size := by
    obtain ⟨qa0, get, size⟩ := blocks.qa
    have eq : qa0 = qa := Option.some.inj (get.symm.trans hq)
    subst qa0
    omega
  have psize : d.w_size.toNat ≤ pa.size := by
    obtain ⟨pa0, get, size⟩ := blocks.pa
    have eq : pa0 = pa := Option.some.inj (get.symm.trans hp)
    subst pa0
    omega
  have mask : d.w_mask.toNat < d.w_size.toNat := by
    have pos : 0 < d.w_size.toNat := by rw [good.inv.wsize]; exact Nat.two_pow_pos _
    rw [good.inv.wmask]
    omega
  exact ⟨w, p, q, wa, pa, qa, ⟨win, hw, blocks.wro, head, hq, prev, hp,
    blocks.pq.symm, hsize, psize, mask, hash_parameters good.inv⟩, H⟩

theorem local_initialized_chains {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32} {cutoff : Nat}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : LocalState (successHeap h r z level a1 a2 a3 qa) cutoff r h.nextBlk
      (resultStream h r z level) (resultState h r level a1 a2 a3)) :
    HeapChains (successHeap h r z level a1 a2 a3 qa) (resultState h r level a1 a2 a3) 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, _⟩ := blocks.pa
  obtain ⟨heads, hq, size⟩ := blocks.qa
  have qid : q = h.nextBlk + 3 := by
    simpa only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
      readyState, allocatedState, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  have eq : heads = clearHead qa 32768 := by
    rw [qid] at hq
    simpa [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW,
      Nat.add_assoc] using hq.symm
  have qs : 32768 ≤ qa.size := by
    rw [eq, size_clearHead] at size
    change qa.size = 32768 at size
    omega
  refine ⟨w, p, q, wa, pa, heads, blocks.win, blocks.prev, blocks.head, hw, hp, hq, ?_⟩
  apply chains_empty
  intro k hk
  change k < 32768 at hk
  rw [eq]
  have zero := clear_head_zero qa 32768 (by decide) qs k hk
  simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]


theorem local_insert_string_chains {h : Heap} {r : ZStreamRef} {cutoff sr wb hb pb top bits : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : LocalState h cutoff r sr z d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (str : UInt32) (current : str = d.strstart) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (window : d.strstart.toNat + d.lookahead.toNat ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after, INSERT_STRING (some (.tab sr)) str h =
        .ok ((wfn ha key.toNat).toUInt32, after) ∧
      LocalState after cutoff r sr z { d with ins_h := key } ∧
      HeapChains after { d with ins_h := key } (str.toNat + 1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key ∧
      after = insertedHeap h sr pb hb d pa ha key := by
  cases current
  obtain ⟨key, run, H, primed⟩ := insert_string_chains good.live.hs env chains d.strstart ws mask
    ordered data window position form
  let pa' := pa.set! (d.strstart &&& d.w_mask).toNat (wfn ha key.toNat)
  let ha' := ha.set! key.toNat d.strstart.toUInt16
  have prevGood := local_words_set good pb pa' pa env.pwords (by simp [pa'])
  have headGood := local_words_set prevGood hb ha' ha
    (by simpa [env.hne] using env.hwords) (by simp [ha'])
  have inv : DStInv _ sr { d with ins_h := key } :=
    { headGood.inv with blocks := headGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have updated := local_state_setD headGood (d' := { d with ins_h := key }) rfl good.live.status inv (by trkeep)
  refine ⟨key, _, run, ?_, H, primed, rfl⟩
  exact updated


theorem local_insert_string_storage {h after : Heap} {r : ZStreamRef} {cutoff ds w q p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa ha pa)
    (str : UInt32) (room : str.toNat + 2 < wa.size) (small : str.toNat + 2 < 2 ^ 32)
    {value : UInt32} (run : INSERT_STRING (some (.tab ds)) str h = .ok (value, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, _hash, _bound, expected⟩ := INSERT_STRING_ok good.live.hs env str room small
  have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
  rw [← eq]
  let linked := setW h p (pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat))
  let headed := setW linked q (ha.set! key.toNat str.toUInt16)
  have shapeP : Shape h linked := shape_setW env.pwords _
  have getQ : linked.words q = some ha := by
    simp only [linked, setW, upd_ne _ _ _ _ env.hne]
    exact env.hwords
  have shapeQ : Shape linked headed := shape_setW getQ _
  have getD : headed.dstates ds = some d := good.live.hs
  have shapeD := shape_setD getD {d with ins_h := key}
  have frameP : Frame h linked (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame h p _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inl env.prevp)))
  have frameQ : Frame linked headed (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame linked q _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl env.headp))))
  have frameD : Frame headed (setD headed ds {d with ins_h := key})
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame headed ds _) (fun _ same => Or.inr (Or.inl same))
  have shape := (shapeP.trans shapeQ).trans shapeD
  have frame := full_frame_trans_shape (full_frame_trans_shape frameP frameQ shapeP) frameD (shapeP.trans shapeQ)
  exact ⟨shape, frame, full_shape_live_change shape, rfl, rfl⟩


/-- Exact typed stores for a concrete inserted heap. This does not merge
objects that happen to use the same numeric owner in different tables. -/
theorem local_inserted_effects {h : Heap} {r : ZStreamRef} {cutoff ds w q p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa ha pa) (key : UInt32) :
    Shape h (insertedHeap h ds p q d pa ha key) ∧
      Frame h (insertedHeap h ds p q d pa ha key) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h (insertedHeap h ds p q d pa ha key) (fun _ => False) (fun _ => False) ∧
      (insertedHeap h ds p q d pa ha key).nalloc = h.nalloc ∧
      (insertedHeap h ds p q d pa ha key).nextBlk = h.nextBlk := by
  let linked := setW h p (pa.set! (d.strstart &&& d.w_mask).toNat (wfn ha key.toNat))
  let headed := setW linked q (ha.set! key.toNat d.strstart.toUInt16)
  have shapeP : Shape h linked := shape_setW env.pwords _
  have getQ : linked.words q = some ha := by
    simp only [linked, setW, upd_ne _ _ _ _ env.hne]
    exact env.hwords
  have shapeQ : Shape linked headed := shape_setW getQ _
  have getD : headed.dstates ds = some d := good.live.hs
  have shapeD := shape_setD getD {d with ins_h := key}
  have frameP : Frame h linked (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame h p _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inl env.prevp)))
  have frameQ : Frame linked headed (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken (word_store_full_frame linked q _)
    intro b same
    subst b
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl env.headp))))
  have frameD : Frame headed (setD headed ds {d with ins_h := key})
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame headed ds _) (fun _ same => Or.inr (Or.inl same))
  have shape := (shapeP.trans shapeQ).trans shapeD
  have frame := full_frame_trans_shape (full_frame_trans_shape frameP frameQ shapeP) frameD (shapeP.trans shapeQ)
  exact ⟨shape, frame, full_shape_live_change shape, rfl, rfl⟩


/-- The same exact insertion, lazy preparation and defer stores retain
all caller typed slots outside the actual stream-owned identities. -/
theorem local_defer_heap_effects {h : Heap} {r : ZStreamRef} {cutoff ds w q p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa ha pa) (key : UInt32) :
    let result := deferOne (lazyPrepare {d with ins_h := key})
    let after := setD (insertedHeap h ds p q d pa ha key) ds result
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have inserted := local_inserted_effects state env key
  have get : (insertedHeap h ds p q d pa ha key).dstates ds = some {d with ins_h := key} := by
    simp [insertedHeap]
  have shape := inserted.1.trans (shape_setD get (deferOne (lazyPrepare {d with ins_h := key})))
  have finalFrame : Frame (insertedHeap h ds p q d pa ha key)
      (setD (insertedHeap h ds p q d pa ha key) ds (deferOne (lazyPrepare {d with ins_h := key})))
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame (insertedHeap h ds p q d pa ha key) ds
      (deferOne (lazyPrepare {d with ins_h := key}))) (fun _ same => Or.inr (Or.inl same))
  exact ⟨shape,full_frame_trans_shape inserted.2.1 finalFrame inserted.1,
    full_shape_live_change shape,rfl,rfl⟩



/-- The hash invariant is produced by the real successful initializer,
including Fresh caller heaps with old cross-table collisions. -/
theorem initialized_hash_chains {h after : Heap} {z : ZStream} {d : DeflateState}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after))
    (localState : LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d) :
    HeapChains after d 0 := by
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
  have chain := local_initialized_chains start.representation
  rw [heaps,sameD] at chain
  exact chain

/-- At positions zero and one the actual inserted chain candidate is NIL.
This follows from actual insertion's older-candidate property, rather than
assuming the matcher is harmless or replacing its source branch. -/
theorem local_nil_search {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (firstTwo : d.strstart.toNat ≤ 1)
    (enough : 262 ≤ d.lookahead.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after,
      slowSearch (some (.tab ds)) h = .ok (0,after) ∧
      LocalState after cutoff r ds z (lazyPrepare {d with ins_h := key}) ∧
      HeapChains after (lazyPrepare {d with ins_h := key}) (d.strstart.toNat+1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat+1) key ∧
      after = setD (insertedHeap h ds p q d pa qa key) ds (lazyPrepare {d with ins_h := key}) := by
  obtain ⟨key,inserted,run,stateI,chainsI,primed,exactHeap⟩ := local_insert_string_chains state env chains d.strstart
    rfl state.inv.wsize state.inv.wmask ordered (by omega) window (by omega) form
  obtain ⟨other,_,expected,older⟩ := insert_candidate_order state.live.hs env chains d.strstart ordered (by omega) (by omega)
  have value := (Prod.mk.inj (Except.ok.inj (run.symm.trans expected))).1
  have nilOther : (wfn qa other.toNat).toNat = 0 := by
    by_cases zero : (wfn qa other.toNat).toNat = 0
    · exact zero
    · have old := older zero; omega
  have nil : (wfn qa key.toNat).toUInt32 = 0 := by
    rw [value]
    apply UInt32.toNat_inj.mp
    change (wfn qa other.toNat).toUInt32.toNat = 0
    simpa only [UInt16.toNat_toUInt32] using nilOther
  let dm := lazyPrepare {d with ins_h := key}
  have stateM := local_state_setD stateI (d' := dm) rfl state.live.status
    (lazy_prepare_inv stateI.inv) (by trkeep)
  have chainsM := lazy_prepare_chains (ds := ds) chainsI
  have find : slowFind (some (.tab ds)) (wfn qa key.toNat).toUInt32 (setD inserted ds dm) =
      .ok ((),setD inserted ds dm) := by
    rw [nil]
    simp [slowFind,bind_app,ldDeflateState_tab stateM.live.hs]
  have ready : d.lookahead ≥ MIN_MATCH_u := by
    change MIN_MATCH_u ≤ d.lookahead
    apply UInt32.le_iff_toNat_le.mpr
    change 3 ≤ d.lookahead.toNat
    omega
  rw [exactHeap] at run find
  have actual := slow_search_composes state.live.hs ready run find
  rw [nil] at actual
  refine ⟨key,_,actual,?_,?_,primed,rfl⟩
  · simpa only [exactHeap] using stateM
  · simpa only [exactHeap] using chainsM

/-- A real complete slow-body iteration inserts the first hash and defers
one byte. The next state and exact consumption arithmetic are on the same
actual execution, without a global caller type-uniqueness premise. -/
theorem local_first_defer {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (firstTwo : d.strstart.toNat ≤ 1)
    (enough : 262 ≤ d.lookahead.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (flush : Int32) (st : LoopS) :
    ∃ key after,
      let result := deferOne (lazyPrepare {d with ins_h := key})
      deflate_slow_body (some (.tab ds)) flush st h =
        .ok ({st with hash_head := 0,bflush := false},after) ∧
      LocalState after cutoff r ds z result ∧
      HeapChains after result (d.strstart.toNat+1) ∧
      result.strstart.toNat = d.strstart.toNat+1 ∧
      result.lookahead.toNat = d.lookahead.toNat-1 ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat+1) key ∧
      after = setD (insertedHeap h ds p q d pa qa key) ds result := by
  obtain ⟨key,searched,search,stateM,chainsM,primed,searchedHeap⟩ :=
    local_nil_search state env chains ordered firstTwo enough window form
  let dm := lazyPrepare {d with ins_h := key}
  let result := deferOne dm
  have counts := advance_one_counts stateM.inv range (by change 1 ≤ d.lookahead.toNat; omega)
  have inv : DStInv searched ds result := {stateM.inv with
    blocks := stateM.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl}
  have next := local_state_setD stateM (d' := result) rfl stateM.live.status inv (by trkeep)
  have nextChains : HeapChains (setD searched ds result) result (d.strstart.toNat+1) := by
    obtain ⟨wb,pb,qb,bytes,prev,heads,win,pp,qp,getW,getP,getQ,H⟩ := chainsM
    refine ⟨wb,pb,qb,bytes,prev,heads,win,pp,qp,getW,getP,getQ,?_⟩
    change HashChains _ _ _ _ _ _ _ _ ((advanceOne dm).strstart.toNat+(advanceOne dm).lookahead.toNat)
    rw [counts.2.2]
    exact H
  have previous : dm.prev_length = 2 := length
  have availableM : dm.match_available = 0 := available
  have decision := slow_defer_run stateM.live.hs previous availableM flush st 0
  have noFill : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]; change ¬d.lookahead.toNat < 262; omega
  refine ⟨key,_,?_,next,nextChains,counts.1,counts.2.1,primed,?_⟩
  · rw [slow_body_source]
    simp only [bind_app,rdD_eq,state.live.hs,noFill,ite_false,search]
    exact decision
  · simp only [searchedHeap,setD_setD]
    rfl

end ZlibF.Spec.Public.Proofs.CompressLocalHash
