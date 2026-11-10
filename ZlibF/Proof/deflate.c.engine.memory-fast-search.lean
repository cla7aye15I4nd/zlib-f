import ZlibF.Proof.«deflate.c.engine.memory-fast-borrow-private»
import ZlibF.Proof.«deflate.c.engine.common-fast-search-short»
import ZlibF.Proof.«deflate.c.engine.common-fast-search»
import ZlibF.Proof.«deflate.c.engine.memory-fast-boundary»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem memory_fast_search_all_full_storage {memory : Nat} {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : MemoryFastBoundary memory h r ds z d input origin base xs config)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ w wa candidate after key pos len,
      fastSearch (some (.tab ds)) h = .ok (candidate, after) ∧
      DGood after r ds z (matchState {d with ins_h := key} pos len) ∧
      HeapChains after (matchState {d with ins_h := key} pos len) (d.strstart.toNat + 1) ∧
      HeapChains after (matchState {d with ins_h := key} pos len)
        (min (d.strstart.toNat + 1) (fillEnd d - 2)) ∧
      d.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      (∀ i, i < fillEnd d → bfn wa i = input (origin + i)) ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → len.toNat ≤ d.lookahead.toNat ∧
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      (3 ≤ d.lookahead.toNat →
        InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key) ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  by_cases three : 3 ≤ d.lookahead.toNat
  · obtain ⟨w0, p, q, wa0, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
    have windowEq : w0 = w := by
      simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
    subst w0
    have arrayEq : wa0 = wa := Option.some.inj (env.wbytes.symm.trans get)
    subst wa0
    obtain ⟨key, after, pos, len, run, goodA, chainsA, bound, matching, bytesA, formA, storage,
        shape, full, live, alloc, next⟩ :=
      fast_search_room_full_storage boundary.good env chains (Nat.le_refl _) boundary.range
        three (room three) boundary.previous_length boundary.match_small (form three)
    have endEq : min (d.strstart.toNat + 1) (fillEnd d - 2) = d.strstart.toNat + 1 :=
      Nat.min_eq_left (by dsimp only [fillEnd]; omega)
    refine ⟨w, wa, _, after, key, pos, len, run, goodA, chainsA, ?_, win, ?_, view, bound,
      matching, (fun _ => formA), bytesA, storage, shape, full, live, alloc, next⟩
    · rw [endEq]; exact chainsA
    · rw [bytesA]; exact get
  · have short : d.lookahead.toNat < 3 := by omega
    have unchanged : matchState {d with ins_h := d.ins_h} d.match_start d.match_length = d := rfl
    have chainsA := heap_chains_raise boundary.chains (Nat.le_add_right d.strstart.toNat 1)
    have endEq : min (d.strstart.toNat + 1) (fillEnd d - 2) =
        min d.strstart.toNat (fillEnd d - 2) := by dsimp only [fillEnd]; omega
    refine ⟨w, wa, 0, h, d.ins_h, d.match_start, d.match_length,
      fast_search_fewer_three boundary.good.live.hs short, ?_, ?_, ?_, win, get, view,
      by have small := boundary.match_small; omega, ?_, (fun enough => by omega), rfl,
      ByteFrame.refl h _, full_storage_refl h _⟩
    · rw [unchanged]; exact boundary.good
    · rw [unchanged]; exact chainsA
    · rw [unchanged, endEq]; exact boundary.end_frontier
    · intro large
      have small := boundary.match_small
      omega


theorem memory_fast_search_initialized_full_storage {memory : Nat} {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : MemoryFastBoundary memory h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ w wa candidate after result,
      fastSearch (some (.tab ds)) h = .ok (candidate, after) ∧
      SearchBoundary after r ds z result input origin base xs w wa ∧
      result = {d with ins_h := result.ins_h, match_start := result.match_start, match_length := result.match_length} ∧
      result.prev_length = 2 ∧ result.match_available = 0 ∧ StreamBuffers after r ∧
      ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w, wa, candidate, after, key, pos, len, run, goodA, chainsA, endA, win, get,
      view, length, matching, primed, bytesA, storage, shape, full, live, alloc, next⟩ :=
    memory_fast_search_all_full_storage boundary room
  let result := matchState {d with ins_h := key} pos len
  have record : result = {d with ins_h := result.ins_h, match_start := result.match_start, match_length := result.match_length} := rfl
  have previous : result.prev_length = 2 := boundary.previous_length
  have noDeferred : result.match_available = 0 := boundary.no_deferred
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  have ledgerA : SymbolLedger buf result xs := ledger.keep rfl rfl rfl rfl
  have getB : after.bytes pb = some buf := by rw [bytesA]; exact trees.base.bytes
  have symbolsA : SymbolBoundary after ds result xs :=
    symbol_boundary_of_ledger goodA trees.base.pbuf getB ledgerA balance
  have frontierA : HeapChains after result (result.strstart.toNat + 1 - result.insert.toNat) := by
    by_cases three : 3 ≤ d.lookahead.toNat
    · have zero := boundary.ready three
      simpa only [result, matchState, zero, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
    · have smallRun := fast_search_fewer_three boundary.good.live.hs (by omega)
      have equal := Except.ok.inj (run.symm.trans smallRun)
      have heaps : after = h := congrArg Prod.snd equal
      have stateEq : result = d := by
        have state := goodA.live.hs
        rw [heaps] at state
        exact Option.some.inj (state.symm.trans boundary.good.live.hs)
      rw [heaps, stateEq]
      exact heap_chains_raise boundary.frontier (by omega)
  have owned := stream_owned_keys boundary.good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read boundary.good.live.hz goodA.live.hz buffers storage
    (fun k equal => (stream_owned_deflate boundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z)
      (Zlib.Deflate.BorrowProofs.Private.stable_fastSearch _ _ _ _ run)
  refine ⟨w, wa, candidate, after, result, run, ?_, record, previous, noDeferred, buffersA,
    storage, shape, full, live, alloc, next⟩
  refine ⟨goodA, chainsA, frontierA, endA, boundary.range, ?_, ?_, symbolsA,
    boundary.insert_le, boundary.ready, win, get, view, length, ?_, ?_, primed, boundary.trace, boundary.accounted⟩
  · unfold PreviousHistory PastMatch
    rw [previous]
    exact ⟨by decide, fun impossible => by change 3 ≤ 2 at impossible; omega⟩
  · intro available
    exact False.elim (available noDeferred)
  · intro large
    exact (matching large).1
  · intro large _
    exact (matching large).2

end Zlib.Deflate.Engine.Proofs

#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_search_all_full_storage

#print axioms Zlib.Deflate.Engine.Proofs.memory_fast_search_initialized_full_storage
