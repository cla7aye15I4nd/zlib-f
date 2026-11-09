import ZlibF.Proof.«compress.c.local-candidate-tail»
import ZlibF.Proof.«compress.c.local-literal-body»

/-! # The actual first literal and general-candidate second literal tail -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralTail
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSearch ZlibF.Spec.Public.Proofs.CompressLocalSearchedLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralBody ZlibF.Spec.Public.Proofs.CompressLocalCandidateTail
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- At initialized position one with 263 buffered bytes, the actual first
literal is followed by a non-NIL-capable candidate search, a second literal
and the actual empty-input return. All three body events share one heap
history and one symbol/resource ledger. -/
theorem two_literal_tail_bodies {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d [])
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (start : d.strstart = 1) (look : d.lookahead = 263)
    (ws : d.w_size = 32768) (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (window : d.strstart.toNat+d.lookahead.toNat ≤ wa.size)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (out : z.avail_out ≠ 0) (length : d.match_length = 2)
    (available : d.match_available ≠ 0) (zero : d.sym_next = 0) (space : 6 < d.sym_end.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ (hash pos len : UInt32) (middle after : Heap) (result : DeflateState),
      let st : LoopS := {hash_head := hash,bflush := false}
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} h = .ok ({},middle) ∧
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} middle = .ok (st,after) ∧
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st after = .ok ({st with ret := some need_more},after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 3 ∧
      SymbolBoundary after ds result [⟨0,wa[0]!.toNat⟩,⟨0,wa[1]!.toNat⟩] ∧
      result.strstart = 3 ∧ result.lookahead = 261 ∧ after.bytes w = some wa ∧
      result.match_start = pos ∧ result.match_length = len ∧ len.toNat ≤ 258 ∧ SlowRecordFrame d result ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have firstRoom : d.sym_next.toNat+3 < d.sym_end.toNat := by rw [zero];change 3 < d.sym_end.toNat;omega
  obtain ⟨nilKey,nilHeap,nilBody,nilState,_nilChains,_nilSymbols,_nilStart,_nilLook,_nilGet,_nilStrict⟩ :=
    local_nil_literal_body state symbol env chains ordered start (by rw [look];decide) window range form
      length available firstRoom out Z_NO_FLUSH {}
  obtain ⟨key1,pos1,len1,middle,first,state1,chains1,symbol1,ss1,la1,_len1,_match1,formed1,get1,record1,
      shape1,frame1,_live1,alloc1,next1⟩ := searched_literal_body state symbol env chains ordered
    (by rw [look];decide) range (by rw [look] at range;change d.strstart.toNat+263 ≤ d.window_size.toNat at range;omega)
    form length available (by rw [start];decide) firstRoom out Z_NO_FLUSH {}
  have heaps : nilHeap = middle := (Prod.mk.inj (Except.ok.inj (nilBody.symm.trans first))).2
  rw [heaps] at nilBody nilState
  let d1 := advanceOne (literalState (matchState (lazyPrepare {d with ins_h := key1}) pos1 len1) wa[d.strstart.toNat-1]!)
  have states := Option.some.inj (nilState.live.hs.symm.trans state1.live.hs)
  have length1 : d1.match_length = 2 := (congrArg DeflateState.match_length states).symm
  have start1 : d1.strstart = 2 := UInt32.toNat_inj.mp (ss1.trans (by rw [start];rfl))
  have look1 : d1.lookahead = 262 := UInt32.toNat_inj.mp (la1.trans (by rw [look];rfl))
  have byte : emittedLiteral d wa = ⟨0,wa[0]!.toNat⟩ := by unfold emittedLiteral;rw [start];rfl
  rw [byte] at symbol1
  have symbols1 : SymbolBoundary middle ds d1 [⟨0,wa[0]!.toNat⟩] := by simpa only [List.nil_append] using symbol1
  obtain ⟨wb,pb,qb,bytes,prev,head,env1,H1⟩ := local_heap_chains_environment state1 chains1
  have wid : wb = w := BRef.blk.inj (Ptr.ref.inj (env1.win.symm.trans env.win)).1
  subst wb
  have array : bytes = wa := Option.some.inj (env1.wbytes.symm.trans get1)
  subst bytes
  have endpoint : d.strstart.toNat+d.lookahead.toNat = 264 := by rw [start,look];decide
  have range1 : d1.strstart.toNat+d1.lookahead.toNat ≤ d1.window_size.toNat := by
    change d1.strstart.toNat+d1.lookahead.toNat ≤ d.window_size.toNat
    rw [start1,look1]
    change 264 ≤ d.window_size.toNat
    omega
  have padding1 : min (d1.strstart.toNat+d1.lookahead.toNat+258) d1.window_size.toNat ≤ d1.high_water.toNat := by
    change min (d1.strstart.toNat+d1.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat
    rw [start1,look1]
    change min 522 d.window_size.toNat ≤ d.high_water.toNat
    simpa only [endpoint] using padded
  have space1 : d1.sym_next.toNat+3 < d1.sym_end.toNat := by
    change (d.sym_next+3).toNat+3 < d.sym_end.toNat
    rw [zero]
    exact space
  have rolling : InsHForm d1.hash_shift d1.hash_mask (bfn wa) d1.strstart.toNat d1.ins_h := by
    change InsHForm d.hash_shift d.hash_mask (bfn wa) d1.strstart.toNat key1
    rw [ss1]
    exact formed1
  obtain ⟨key2,pos2,len2,after,result,second,third,state2,chains2,symbol2,start2,look2,get2,matchPos,matchLen,lenBound,
      record2,shape2,frame2,_live2,alloc2,next2⟩ := candidate_tail_bodies state1 symbols1 env1 H1
    (by rw [ss1];omega) start1 look1 ws range1 padding1 input out length1 available space1 rolling
  have frame2' : Frame middle after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) := frame2
  have shape := shape1.trans shape2
  have frame := full_frame_trans_shape frame1 frame2' shape1
  exact ⟨(wfn head key2.toNat).toUInt32,pos2,len2,middle,after,result,nilBody,second,third,state2,chains2,symbol2,start2,look2,get2,
    matchPos,matchLen,lenBound,record1.trans record2,shape,frame,full_shape_live_change shape,alloc2.trans alloc1,next2.trans next1⟩

end ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralTail
