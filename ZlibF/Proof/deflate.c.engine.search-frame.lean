import ZlibF.Proof.«deflate.c.engine.short-search»
import ZlibF.Proof.«deflate.c.engine.strategy-boundary»

/-! # Every lookahead length has an actual search cutpoint for finishing -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Search changes lazy match fields and the rolling key only. -/
def SearchWorkFrame (before after : DeflateState) : Prop :=
  after = { before with
    ins_h := after.ins_h, match_start := after.match_start, match_length := after.match_length,
    prev_match := after.prev_match, prev_length := after.prev_length }

/-- Actual search, including the fewer-than-three-byte path, retains
previous-match history and the exact symbol ledger. A new length of at
least three fits real lookahead. An improving match has matching window
bytes. Physical comparison room is needed only if insertion/search runs.
This is the search cutpoint, not the final strategy call. -/
theorem slow_search_all_frame {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
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
      SlowRecordFrame d result ∧ SearchWorkFrame d result ∧ ByteFrame h after (fun i => i = ds) := by
  have pack {candidate key pos len : UInt32} {after : Heap}
      (run : slowSearch (some (.tab ds)) h = .ok (candidate, after))
      (goodA : DGood after r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len))
      (chainsA : HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1))
      (bytesA : after.bytes = h.bytes) (length : len.toNat ≤ 258)
      (clipped : 3 ≤ len.toNat → len.toNat ≤ d.lookahead.toNat)
      (matching : 3 ≤ len.toNat → d.match_length.toNat < len.toNat →
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat)
      (formA : 3 ≤ d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key)
      (storage : ByteFrame h after (fun i => i = ds)) :
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
        SlowRecordFrame d result ∧ SearchWorkFrame d result ∧ ByteFrame h after (fun i => i = ds) := by
    let result := matchState (lazyPrepare { d with ins_h := key }) pos len
    obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
    have getB : after.bytes b = some buf := by rw [bytesA]; exact trees.base.bytes
    have ledgerA : SymbolLedger buf result xs := ledger.keep rfl rfl rfl rfl
    have symbols : SymbolBoundary after ds result xs :=
      symbol_boundary_of_ledger goodA trees.base.pbuf getB ledgerA balance
    have previous : PreviousHistory input origin result := logical_prepare_history boundary.history key
    refine ⟨candidate, after, result, run, goodA, chainsA, win, ?_, previous, boundary.deferred,
      symbols, length, clipped, matching, formA, ?_, rfl, storage⟩
    · rw [bytesA]; exact get
    · rfl
  by_cases three : 3 ≤ d.lookahead.toNat
  · obtain ⟨w0, p, q, wa0, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
    have windowEq : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
    subst w0
    have arrayEq : wa0 = wa := Option.some.inj (env.wbytes.symm.trans get)
    subst wa0
    obtain ⟨wv, wbytes, pointerV, bytesV, _view, hashForm⟩ := boundary.data
    have windowV : wv = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using pointerV.symm
    subst wv
    have arrayV : wbytes = wa := Option.some.inj (bytesV.symm.trans get)
    subst wbytes
    obtain ⟨key, after, pos, len, run, goodA, chainsA, bound, clipped, matching, bytesA, formA, storage⟩ :=
      slow_search_room_storage boundary.good env chains (Nat.le_refl _) boundary.range three (room three)
        boundary.history.1 (hashForm three)
    exact pack run goodA chainsA bytesA bound (fun _ => clipped) matching (fun _ => formA) storage
  · have short : d.lookahead.toNat < 3 := by omega
    obtain ⟨run, goodA, chainsA, storage⟩ := slow_search_fewer_three boundary.good boundary.chains short
    have raised := heap_chains_raise chainsA (Nat.le_add_right d.strstart.toNat 1)
    refine pack (key := d.ins_h) (pos := d.match_start) (len := 2) run goodA raised rfl (by decide) ?_ ?_ ?_ storage
    · intro large
      change 3 ≤ 2 at large
      omega
    · intro large
      change 3 ≤ 2 at large
      omega
    · intro enough
      omega

end Zlib.Deflate.Engine.Proofs
