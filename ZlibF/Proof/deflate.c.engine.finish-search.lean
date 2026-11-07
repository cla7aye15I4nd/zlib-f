import ZlibF.Proof.«deflate.c.engine.search-frame»

/-! # Every lookahead length has an actual search cutpoint for finishing -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The earlier cutpoint follows from the stronger actual search frame. -/
theorem slow_search_all_lookahead {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ candidate after result,
      slowSearch (some (.tab ds)) h = .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result (d.strstart.toNat + 1) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      PreviousHistory input origin result ∧ DeferredByte result ∧ SymbolBoundary after ds result xs ∧
      result.match_length.toNat ≤ 258 ∧
      (3 ≤ result.match_length.toNat → result.match_length.toNat ≤ d.lookahead.toNat) ∧
      (3 ≤ result.match_length.toNat → result.prev_length.toNat < result.match_length.toNat →
        GoodMatch wa result.strstart.toNat result.w_size.toNat result.match_start.toNat result.match_length.toNat) ∧
      (3 ≤ d.lookahead.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      SlowRecordFrame d result ∧ ByteFrame h after (fun i => i = ds) := by
  obtain ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, previous, deferred,
      symbols, length, clipped, matching, formA, slowFrame, _searchFrame, storage⟩ :=
    slow_search_all_frame boundary win get room
  exact ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, previous, deferred,
    symbols, length, clipped, matching, formA, slowFrame, storage⟩

end Zlib.Deflate.Engine.Proofs
