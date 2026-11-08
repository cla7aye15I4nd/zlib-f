import ZlibF.Proof.«deflate.c.engine.strategy-encoding-cut»
import ZlibF.Proof.«deflate.c.engine.short-literal-boundary»
import ZlibF.Proof.«deflate.c.engine.public-output-bytes»

/-! # Nonpublishing literal and defer decisions preserve the actual held bits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A real nonpublishing state frame with zero pending bytes preserves
the entire held-word bit sequence. Returned caller ranges identify the
empty delivered-byte slice. These are mathematical heap/state facts. -/
theorem slow_record_zero_pending_bits {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d result : DeflateState} {before : List Bool}
    (goodA : DGood after r ds z result) (buffersA : StreamBuffers after r)
    (frame : SlowRecordFrame d result) (pointer : z.next_out = .ref (.blk ob) oo)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf)
    (pendingBefore : PendingBits h d before) :
    Bytes after z.next_out 0 [] ∧ PendingBits after result before := by
  obtain ⟨state, pb, buf, trees⟩ := goodA.trees
  have same : state = result := Option.some.inj (trees.base.dstate.symm.trans goodA.live.hs)
  subst state
  have cursorA : result.pending_out = result.pending_buf := by rw [frame]; exact cursor
  have zeroA : result.pending = 0 := by rw [frame]; exact pending
  have bitsA := pending_bits_base trees cursorA
  have valueA := pending_bits_zero_value zeroA bitsA
  have valueBefore := pending_bits_zero_value pending pendingBefore
  have word : result.bi_buf = d.bi_buf := by rw [frame]
  have count : result.bi_valid = d.bi_valid := by rw [frame]
  rw [word, count] at valueA
  have sameBits : Zlib.Trees.Proofs.Out.outBits buf result = before := valueA.trans valueBefore.symm
  rw [sameBits] at bitsA
  obtain ⟨written, bytesA, length⟩ := accounted_output_bytes goodA.live.hz buffersA pointer (stream_accounting_zero z)
  have emptyWritten : written = [] := by
    cases written with
    | nil => rfl
    | cons _ _ => simp at length
  rw [emptyWritten] at bytesA
  exact ⟨bytesA, bitsA⟩

/-- The actual nonfull deferred-literal decision extends the symbol
ledger and preserves every held bit. Both caller-output return branches
retain the same content and EOF frontiers, including short input. -/
theorem slow_literal_nonfull_search_encoding {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ after result before,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z.avail_out == 0 then { st with hash_head := candidate, bflush := false, ret := some need_more }
          else { st with hash_head := candidate, bflush := false }), after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [emittedLiteral d wa]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z 0 0 ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ PublishReady result ∧
      PendingBits h d before ∧ Bytes after z.next_out 0 [] ∧ PendingBits after result before := by
  obtain ⟨after, result, run, boundaryA, endA, buffersA, frame, startA, lookA,
    endpoint, strictA, _storage⟩ :=
    slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := cut.symbols
  have pendingBefore := pending_bits_base trees cursor
  obtain ⟨bytesA, bitsA⟩ := slow_record_zero_pending_bits boundaryA.good buffersA frame pointer pending cursor pendingBefore
  have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, bits⟩) frame
  exact ⟨after, result, Zlib.Trees.Proofs.Out.outBits buf d, run, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, pendingBefore, bytesA, bitsA⟩

/-- The actual no-symbol defer branch advances one byte without changing
any output bit. Its pending input credit, both chain frontiers and caller
ranges are the actual returned state, including at the last input byte. -/
theorem slow_defer_search_encoding {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ after result before,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := candidate, bflush := false }, after) ∧
      ContentBoundary after r ds z result input origin base xs ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z 0 0 ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ PublishReady result ∧
      PendingBits h d before ∧ Bytes after z.next_out 0 [] ∧ PendingBits after result before := by
  obtain ⟨after, result, run, boundaryA, endA, buffersA, frame, startA, lookA,
    endpoint, strictA, _storage⟩ :=
    slow_defer_search_boundary cut buffers lookahead branch available strict flush st candidate
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := cut.symbols
  have pendingBefore := pending_bits_base trees cursor
  obtain ⟨bytesA, bitsA⟩ := slow_record_zero_pending_bits boundaryA.good buffersA frame pointer pending cursor pendingBefore
  have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, bits⟩) frame
  exact ⟨after, result, Zlib.Trees.Proofs.Out.outBits buf d, run, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, pendingBefore, bytesA, bitsA⟩

end Zlib.Deflate.Engine.Proofs
