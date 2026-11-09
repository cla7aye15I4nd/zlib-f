import ZlibF.Proof.«compress.c.local-literal-storage»
import ZlibF.Proof.«compress.c.local-literal-loop»

/-! # Full typed effects and owned roots on the same actual slow bodies -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalBodyResources
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody ZlibF.Spec.Public.Proofs.CompressLocalLiteralStorage
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The actual insertion stores followed by a private record store preserve
all typed slots outside the same original private footprint. -/
theorem inserted_final_resources {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (key : UInt32) (result : DeflateState) :
    let after := setD (insertedHeap h ds p q d pa qa key) ds result
    Shape h after ∧ Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have inserted := local_inserted_effects state env key
  have get : (insertedHeap h ds p q d pa qa key).dstates ds = some {d with ins_h := key} := by simp [insertedHeap]
  have shape := inserted.1.trans (shape_setD get result)
  have frame : Frame (insertedHeap h ds p q d pa qa key)
      (setD (insertedHeap h ds p q d pa qa key) ds result)
      (fun x => StreamRoot r x ∨ DeflateOwned ds d x) :=
    full_frame_weaken (state_store_full_frame _ ds result) (fun _ same => Or.inr (Or.inl same))
  exact ⟨shape,full_frame_trans_shape inserted.2.1 frame inserted.1,rfl,rfl⟩

/-- Storage and owned-root preservation for an observed complete first
literal body. Its execution is constructed from actual insertion and the
actual nonfull literal producer before matching the observed returned heap.
The observed run is an event, not a callee specification assumption. -/
theorem nil_literal_body_resources {h after : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z za : ZStream} {d da : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {next : LoopS}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (position : d.strstart = 1)
    (enough : 262 ≤ d.lookahead.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (length : d.match_length = 2) (available : d.match_available ≠ 0)
    (space : d.sym_next.toNat+3 < d.sym_end.toNat) (out : z.avail_out ≠ 0)
    (flush : Int32) (st : LoopS)
    (actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (next,after))
    (returned : DLive after r ds za da) :
    SlowRecordFrame d da ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key,searched,search,stateM,chainsM,_primed,searchHeap⟩ :=
    local_nil_search state env chains ordered (by rw [position];decide) enough window form
  let dm := lazyPrepare {d with ins_h := key}
  have get : searched.bytes w = some wa := by simpa [searchHeap,insertedHeap] using env.wbytes
  have previous : 1 ≤ dm.strstart.toNat := by change 1 ≤ d.strstart.toNat;rw [position];decide
  have branch : (dm.prev_length ≥ MIN_MATCH_u && dm.match_length ≤ dm.prev_length) = false := by
    change (d.match_length ≥ MIN_MATCH_u && (2 : UInt32) ≤ d.match_length) = false
    rw [length];decide
  obtain ⟨expected,decision,stateA,_chains,_range,_get,_strict,_record,_win,_prev,_head,_pending,
      shapeL,frameL,_live,allocL,nextL,_canonical⟩ :=
    local_slow_literal_full_storage stateM chainsM env.win get range (by change 1 ≤ d.lookahead.toNat;omega)
      previous branch available space flush st 0
  have notFull : (z.avail_out == 0) = false := beq_eq_false_iff_ne.mpr out
  simp only [notFull,Bool.false_eq_true,ite_false] at decision
  have noFill : ¬d.lookahead < MIN_LOOKAHEAD_u := by rw [UInt32.lt_iff_toNat_lt];change ¬d.lookahead.toNat < 262;omega
  have expectedBody : deflate_slow_body (some (.tab ds)) flush st h =
      .ok ({st with hash_head := 0,bflush := false},expected) := by
    rw [slow_body_source]
    simp only [bind_app,rdD_eq,state.live.hs,noFill,ite_false,search]
    exact decision
  have heaps := (Prod.mk.inj (Except.ok.inj (expectedBody.symm.trans actual))).2
  have getD := stateA.live.hs
  rw [heaps] at getD
  have states := Option.some.inj (getD.symm.trans returned.hs)
  have record : SlowRecordFrame d da := by
    rw [←states]
    rfl
  have searchEffects := inserted_final_resources state env key dm
  have shapeS : Shape h searched := by simpa only [searchHeap] using searchEffects.1
  have frameS : Frame h searched (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := by
    simpa only [searchHeap] using searchEffects.2.1
  have frameL' : Frame searched expected (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := frameL
  have shape := shapeS.trans shapeL
  have frame := full_frame_trans_shape frameS frameL' shapeS
  have nalloc : expected.nalloc = h.nalloc := by simpa [searchHeap,insertedHeap] using allocL
  have nextBlk : expected.nextBlk = h.nextBlk := by simpa [searchHeap,insertedHeap] using nextL
  rw [heaps] at shape frame nalloc nextBlk
  exact ⟨record,shape,frame,full_shape_live_change shape,nalloc,nextBlk⟩

/-- The corresponding actual first defer body retains its exact typed
footprint and buffer roots on the observed returned state. -/
theorem first_defer_body_resources {h after : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z za : ZStream} {d da : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16} {next : LoopS}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (firstTwo : d.strstart.toNat ≤ 1)
    (enough : 262 ≤ d.lookahead.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (flush : Int32) (st : LoopS)
    (actual : deflate_slow_body (some (.tab ds)) flush st h = .ok (next,after))
    (returned : DLive after r ds za da) :
    SlowRecordFrame d da ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key,expected,expectedBody,nextState,_chains,_start,_look,_form,exactHeap⟩ :=
    local_first_defer state env chains ordered firstTwo enough window range form length available flush st
  have heaps := (Prod.mk.inj (Except.ok.inj (expectedBody.symm.trans actual))).2
  have getD := nextState.live.hs
  rw [heaps] at getD
  have states := Option.some.inj (getD.symm.trans returned.hs)
  have record : SlowRecordFrame d da := by rw [←states];rfl
  have effects := local_defer_heap_effects state env key
  dsimp only at effects
  rw [←exactHeap,heaps] at effects
  exact ⟨record,effects⟩

/-- The same record relation supplies all four addresses required by the
actual End/free proof; no caller-side uniqueness condition is introduced. -/
theorem record_owned_keys {d da : DeflateState} (record : SlowRecordFrame d da) :
    da.window = d.window ∧ da.prev = d.prev ∧ da.head = d.head ∧ da.pending_buf = d.pending_buf := by
  unfold SlowRecordFrame at record
  rw [record]
  exact ⟨rfl,rfl,rfl,rfl⟩

end ZlibF.Spec.Public.Proofs.CompressLocalBodyResources
