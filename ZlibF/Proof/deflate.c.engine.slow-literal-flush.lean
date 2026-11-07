import ZlibF.Proof.«deflate.c.engine.slow-literal-loop»

/-! # The actual full-buffer deferred-literal decision -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The full deferred-literal branch executes its real tally, unrestricted
flush, publication, one-byte advance and output-full return. The tally
repays the deferred byte before flush; the subsequent advance restores
credit one. Zero and short caller output capacities are included.
This is a selected decision cutpoint, not the entire slow loop. -/
theorem slow_literal_full_flush {h : Heap} {r : ZStreamRef} {ds pb ob oo w top origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (chains : HeapChains h d top) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (lookahead : 1 ≤ d.lookahead.toNat)
    (previousByte : 1 ≤ d.strstart.toNat) (balance : BlockBalance d xs 1)
    (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head, bflush := true, ret := some need_more }
          else { st with hash_head, bflush := true }), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      HeapChains after result top ∧ result.window = .ref (.blk w) 0 ∧ after.bytes w = some window ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next = 0 ∧ BlockInit.BlockClear result ∧ SymbolBoundary after ds result [] ∧
      FlushWorkFrame { advanceOne d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      base + represented (xs ++ [emittedLiteral d window]) + 1 = origin + result.strstart.toNat := by
  obtain ⟨produced, after, z', result, run, goodA, buffersA, accountA, chainsA, winA, bytesA, startA, lookA, endpoint, countA, clearA, symbolsA, frameA, accountedA, _config, _low, _phase⟩ :=
    slow_literal_full_flush_loop good trees buffers chains positive pointer cursor memory pending bits ledger clear trace
      win get range lookahead previousByte balance accounted view literalBranch available full flush st hash_head
  exact ⟨produced, after, z', result, run, goodA, buffersA, accountA, chainsA, winA, bytesA, startA, lookA, endpoint, countA, clearA, symbolsA, frameA, accountedA⟩

/-- At the search/decision cutpoint, the supplied next-position hash and
logical-match facts let the real full literal branch re-establish the
initialized content boundary. These are mathematical state facts, not
contracts for the tally, flush or advance callees. -/
theorem slow_literal_full_flush_content {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (chains : HeapChains h d (d.strstart.toNat + 1)) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (lookahead : 1 ≤ d.lookahead.toNat)
    (previousByte : 1 ≤ d.strstart.toNat) (balance : BlockBalance d xs 1)
    (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) 
    (insert : d.insert = 0) (history : LazyHistory input origin (advanceOne d))
    (form : InsHForm d.hash_shift d.hash_mask (bfn window) (d.strstart.toNat + 1) d.ins_h) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head, bflush := true, ret := some need_more }
          else { st with hash_head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin
        (base + represented (xs ++ [emittedLiteral d window])) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d := by
  obtain ⟨produced, after, z', result, run, state, buffersA, accountA, clearA, startA, lookA, endpoint, _config, _low, _phase⟩ :=
    slow_literal_full_flush_loop_content good trees buffers chains positive pointer cursor memory pending bits ledger clear trace
      win get range lookahead previousByte balance accounted view literalBranch available full flush st hash_head insert history form
  exact ⟨produced, after, z', result, run, state, buffersA, accountA, clearA, startA, lookA, endpoint⟩

end Zlib.Deflate.Engine.Proofs
