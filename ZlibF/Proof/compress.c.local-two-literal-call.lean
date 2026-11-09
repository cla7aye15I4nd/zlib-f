import ZlibF.Proof.«compress.c.local-two-literal-tail»
import ZlibF.Proof.«compress.c.local-loop-resources»

/-! # A complete real buffered call containing a non-NIL-capable search -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralCall
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody ZlibF.Spec.Public.Proofs.CompressLocalBodyResources
open ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralTail
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Four actual loop bodies defer one byte, emit two literals and return
need_more. Source bytes are arbitrary; the third insertion may select an
active nonzero history candidate. Entry facts are internal history facts. -/
theorem slow_two_literal_call {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d [])
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat 0 (d.strstart.toNat+d.lookahead.toNat))
    (start : d.strstart = 0) (look : d.lookahead = 264) (ws : d.w_size = 32768)
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (out : z.avail_out ≠ 0)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (zero : d.sym_next = 0) (space : 6 < d.sym_end.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more,after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 3 ∧
      SymbolBoundary after ds result [⟨0,wa[0]!.toNat⟩,⟨0,wa[1]!.toNat⟩] ∧
      result.strstart = 3 ∧ result.lookahead = 261 ∧ after.bytes w = some wa ∧
      SlowRecordFrame d result ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key1,after1,first,state1,chains1,ss1,la1,form1,exact1⟩ :=
    local_first_defer state env chains (by simp [start]) (by simp [start])
      (by rw [look]; decide) window range form length available Z_NO_FLUSH {}
  let d1 := deferOne (lazyPrepare {d with ins_h := key1})
  have symbol1 := local_first_defer_symbols state1 symbol available ss1 exact1
  have start1 : d1.strstart = 1 := UInt32.toNat_inj.mp (ss1.trans (by rw [start]; rfl))
  have look1 : d1.lookahead = 263 := UInt32.toNat_inj.mp (la1.trans (by rw [look]; rfl))
  have get1 : after1.bytes w = some wa := by simpa [exact1,insertedHeap] using env.wbytes
  obtain ⟨wb,pb,qb,bytes,prev,head,env1,H1⟩ := local_heap_chains_environment state1 chains1
  have wid : wb = w := BRef.blk.inj (Ptr.ref.inj (env1.win.symm.trans env.win)).1
  subst wb
  have array : bytes = wa := Option.some.inj (env1.wbytes.symm.trans get1)
  subst bytes
  have range1 : d1.strstart.toNat+d1.lookahead.toNat ≤ d1.window_size.toNat := by
    change d1.strstart.toNat+d1.lookahead.toNat ≤ d.window_size.toNat
    rw [start1,look1]
    change 264 ≤ d.window_size.toNat
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 264 := by rw [start,look]; decide
    omega
  have window1 : d1.strstart.toNat+d1.lookahead.toNat ≤ wa.size := by
    rw [start1,look1]
    change 264 ≤ wa.size
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 264 := by rw [start,look]; decide
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
    change min 522 d.window_size.toNat ≤ d.high_water.toNat
    have endpoint : d.strstart.toNat+d.lookahead.toNat = 264 := by rw [start,look]; decide
    simpa only [endpoint] using padded
  obtain ⟨hash,pos,len,middle,after2,result,second,third,fourth,state2,chains2,symbol2,ss2,look2,get2,_pos,_len,_bound,
      record2,shape2,frame2,live2,alloc2,next2⟩ :=
    two_literal_tail_bodies (d := d1) state1 symbol1 env1 H1 ordered start1 look1 ws range1 window1 padding1
      input out (by rfl) (by change (1 : Int32) ≠ 0; decide) zero space rolling
  let st : LoopS := {hash_head := hash,bflush := false}
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h =
      .ok ({st with ret := some need_more},after2) := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551611+5) {} h = _
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551611+4) x) h = _
    rw [bind_app,first]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551611+3) x) after1 = _
    rw [bind_app,second]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551611+2) x) middle = _
    rw [bind_app,third]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) (18446744073709551611+1) x) after2 = _
    rw [bind_app,fourth]
    simp only []
    rw [cwhile.go]
    rfl
  have firstEffects := first_defer_body_resources state env chains (by simp [start]) (by simp [start])
    (by rw [look];decide) window range form length available Z_NO_FLUSH {} first state1.live
  obtain ⟨record1,shape1,frame1,_live1,alloc1,next1⟩ := firstEffects
  have frame2' : Frame after1 after2 (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := by
    apply full_frame_weaken frame2
    intro x member
    rcases member with root | owned
    · exact Or.inl root
    · right
      exact owned
  have shape := shape1.trans shape2
  have frame := full_frame_trans_shape frame1 frame2' shape1
  refine ⟨after2,result,?_,state2,chains2,symbol2,ss2,look2,get2,record1.trans record2,shape,frame,
    full_shape_live_change shape,alloc2.trans alloc1,next2.trans next1⟩
  unfold deflate_slow
  rw [bind_app,loop]
  rfl


end ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralCall
