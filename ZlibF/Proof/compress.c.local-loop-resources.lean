import ZlibF.Proof.«compress.c.local-body-resources»

/-! # Complete resource and owned-root preservation of the real first literal call -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLoopResources
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody ZlibF.Spec.Public.Proofs.CompressLocalThreshold
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop ZlibF.Spec.Public.Proofs.CompressLocalBodyResources
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem literal_tail_resources {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
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
      result.strstart = 2 ∧ result.lookahead = 261 ∧ after.bytes w = some wa ∧
      SlowRecordFrame d result ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨after,result,body,resumed,stateA,chainsA,symbolsA,ss,la,get⟩ :=
    local_literal_tail_bodies state symbol env chains ordered start look ws range window padded input out length available space form
  have effects := nil_literal_body_resources state env chains ordered start (by rw [look];decide)
    window range form length available space out Z_NO_FLUSH {} body stateA.live
  exact ⟨after,result,body,resumed,stateA,chainsA,symbolsA,ss,la,get,effects⟩

theorem slow_literal_call_resources {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
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
      result.strstart = 2 ∧ result.lookahead = 261 ∧ after.bytes w = some wa ∧
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
  obtain ⟨after2,result,second,third,state2,chains2,symbol2,ss2,look2,get2,record2,shape2,frame2,live2,alloc2,next2⟩ :=
    literal_tail_resources (d := d1) state1 symbol1 env1 H1 ordered start1 look1 ws range1 window1 padding1
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


end ZlibF.Spec.Public.Proofs.CompressLocalLoopResources
