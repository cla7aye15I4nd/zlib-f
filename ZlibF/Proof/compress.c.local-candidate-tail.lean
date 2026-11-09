import ZlibF.Proof.«compress.c.local-searched-literal»
import ZlibF.Proof.«compress.c.local-threshold»

/-! # A real non-NIL-capable literal tail and empty-input return -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalCandidateTail
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSearchedLiteral ZlibF.Spec.Public.Proofs.CompressLocalThreshold
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- At the third initialized position, real search may have an old
nonzero head. The actual literal body is followed by the actual empty
refill/need_more return on the same heap and symbol ledger. -/
theorem candidate_tail_bodies {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16} {xs : List Symbol}
    (state : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat+d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat) (start : d.strstart = 2) (look : d.lookahead = 262)
    (ws : d.w_size = 32768) (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (out : z.avail_out ≠ 0) (length : d.match_length = 2)
    (available : d.match_available ≠ 0) (space : d.sym_next.toNat+3 < d.sym_end.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ (key pos len : UInt32) (after : Heap) (result : DeflateState),
      let st : LoopS := {hash_head := (wfn qa key.toNat).toUInt32,bflush := false}
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} h = .ok (st,after) ∧
      deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st after = .ok ({st with ret := some need_more},after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result 3 ∧
      SymbolBoundary after ds result (xs++[⟨0,wa[1]!.toNat⟩]) ∧
      result.strstart = 3 ∧ result.lookahead = 261 ∧ after.bytes w = some wa ∧
      result.match_start = pos ∧ result.match_length = len ∧ len.toNat ≤ 258 ∧ SlowRecordFrame d result ∧ Shape h after ∧
      Frame h after (fun x => StreamRoot r x ∨ DeflateOwned ds d x) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key,pos,len,after,body,stateA,chainsA,symbolA,ss,la,lenBound,_matching,_formed,get,record,
      shape,frame,live,alloc,next⟩ := searched_literal_body state symbol env chains ordered (by rw [look];decide)
    range (by simpa only [look,show (262 : UInt32).toNat = 262 from rfl] using range) form length available (by rw [start];decide) space out Z_NO_FLUSH {}
  let result := advanceOne (literalState (matchState (lazyPrepare {d with ins_h := key}) pos len) wa[d.strstart.toNat-1]!)
  let st : LoopS := {hash_head := (wfn qa key.toNat).toUInt32,bflush := false}
  have startA : result.strstart = 3 := UInt32.toNat_inj.mp (ss.trans (by rw [start];rfl))
  have lookA : result.lookahead = 261 := UInt32.toNat_inj.mp (la.trans (by rw [look];rfl))
  have keys : result.window_size = d.window_size ∧ result.high_water = d.high_water ∧ result.w_size = d.w_size := ⟨rfl,rfl,rfl⟩
  have endpoint : d.strstart.toNat+d.lookahead.toNat = 264 := by rw [start,look];decide
  have rangeA : result.strstart.toNat+result.lookahead.toNat ≤ result.window_size.toNat := by
    rw [startA,lookA,keys.1]
    change 264 ≤ d.window_size.toNat
    omega
  have noSlide : ¬result.strstart ≥ result.w_size+(result.w_size-MIN_LOOKAHEAD_u) := by
    rw [startA,keys.2.2,ws];decide
  have paddingA : min (result.strstart.toNat+result.lookahead.toNat+258) result.window_size.toNat ≤ result.high_water.toNat := by
    rw [startA,lookA,keys.1,keys.2.1]
    change min 522 d.window_size.toNat ≤ d.high_water.toNat
    simpa only [endpoint] using padded
  have resumed := local_slow_resume_short_body stateA input noSlide rangeA paddingA (by rw [lookA];decide) st
  have top : d.strstart.toNat+1 = 3 := by rw [start];decide
  rw [top] at chainsA
  have byte : emittedLiteral d wa = ⟨0,wa[1]!.toNat⟩ := by
    unfold emittedLiteral
    rw [start]
    rfl
  rw [byte] at symbolA
  have symbols : SymbolBoundary after ds result (xs++[⟨0,wa[1]!.toNat⟩]) := symbolA
  exact ⟨key,pos,len,after,result,body,resumed,stateA,chainsA,symbols,startA,lookA,get,rfl,rfl,lenBound,
    record,shape,frame,live,alloc,next⟩

end ZlibF.Spec.Public.Proofs.CompressLocalCandidateTail
