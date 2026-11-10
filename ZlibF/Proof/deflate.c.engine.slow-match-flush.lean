import ZlibF.Proof.«deflate.c.engine.slow-match-loop»

/-! # The actual full match decision consumes the match before flushing -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real selected-match decision fills the symbol buffer, executes
the complete match-consumption/insertion loop, then flushes and obeys the
actual need_more return. Logical previous-match bytes supply the emitted
symbol's meaning. This is an internal selected decision cutpoint. -/
theorem slow_match_full_flush {h : Heap} {r : ZStreamRef} {ds ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (buffers : StreamBuffers h r)
    (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (lookahead : 262 ≤ d.lookahead.toNat) (range : fillEnd d ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (full : d.sym_next.toNat + 3 = d.sym_end.toNat) (insert : d.insert = 0)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (trace : Trace input base xs) (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ (produced : Nat) (head : UInt32) (after : Heap) (z' : ZStream) (result : DeflateState),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedMatch d])) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d := by
  obtain ⟨produced, head, after, z', result, run, state, buffersA, accountA, clearA, startA, lookA, endpoint, _config, _low, _phase⟩ :=
    slow_match_full_flush_loop good symbol buffers chains win get history selected lookahead range form full insert positive
      pointer cursor memory pending bits clear trace accounted view flush st hash_head
  exact ⟨produced, head, after, z', result, run, state, buffersA, accountA, clearA, startA, lookA, endpoint⟩

end Zlib.Deflate.Engine.Proofs
