import ZlibF.Proof.«compress.c.local-match-advance»

/-! # Actual ordinary selected-match consumption at the local boundary -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchOrdinary
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalMatchAdvance
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The ordinary entry supplies at least MIN_LOOKAHEAD bytes. The actual
bounded-consumption producer therefore retains at least three real bytes
and its next rolling hash is unconditional. -/
theorem local_match_advance_storage {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head h =
        .ok (candidate, after) ∧
      LocalState after cutoff r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.match_available = 0 ∧ result.match_length = 2 ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      TrKeep d result ∧ result.high_water = d.high_water ∧ after.bytes = h.bytes ∧
      result.block_start = d.block_start ∧ result.dyn_ltree = d.dyn_ltree ∧ result.dyn_dtree = d.dyn_dtree ∧
      result = { d with
        strstart := result.strstart, lookahead := result.lookahead, ins_h := result.ins_h,
        prev_length := result.prev_length, match_available := 0, match_length := 2 } ∧ ByteFrame h after (fun i => i = ds) := by
  have frontier : min (d.strstart.toNat+1) (d.strstart.toNat+d.lookahead.toNat-2) = d.strstart.toNat+1 :=
    Nat.min_eq_left (by omega)
  have saved : HeapChainsAt h d (min (d.strstart.toNat+1) (d.strstart.toNat+d.lookahead.toNat-2))
      (d.strstart.toNat+d.lookahead.toNat) := by rw [frontier];exact chains.at
  obtain ⟨candidate,after,result,actual,stateA,chainsA,_frontier,winA,getA,availableA,lengthA,previousA,
      startA,lookA,endpoint,rangeA,formA,keep,high,bytes,block,literal,distance,record,frame⟩ :=
    local_match_advance good saved win get previous length (by omega) (by omega) range (fun _ => form) hash_head
  refine ⟨candidate,after,result,actual,stateA,chainsA,winA,getA,availableA,lengthA,previousA,startA,lookA,
    endpoint,rangeA,formA ?_,keep,high,bytes,block,literal,distance,record,frame⟩
  rw [lookA]
  omega

end ZlibF.Spec.Public.Proofs.CompressLocalMatchOrdinary
