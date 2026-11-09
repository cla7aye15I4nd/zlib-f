import ZlibF.Proof.«deflate.c.engine.nonpublishing-decision-encoding»
import ZlibF.Proof.«deflate.c.engine.match-nonfull-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A legal non-null caller output view admits its empty prefix, independently of the reference variant. -/
theorem caller_empty_output_view {h : Heap} {r : ZStreamRef} {z : ZStream} {ref : BRef} {off : Nat}
    (get : r.get h = some z) (buffers : StreamBuffers h r) (pointer : z.next_out = .ref ref off) :
    Bytes h z.next_out 0 [] := by
  obtain ⟨other,otherGet,_,output,_⟩ := buffers
  have same : other=z := Option.some.inj (otherGet.symm.trans get)
  subst other
  rcases output with null | ⟨⟨xs,bytes⟩,_,_⟩
  · rw [pointer] at null
    contradiction
  · rcases bytes with ⟨null,_,_⟩ | ⟨view,i,a,ptr,array,bound,_⟩
    · rw [pointer] at null
      contradiction
    · exact Or.inr ⟨view,i,a,ptr,array,by omega,by simp⟩

theorem generic_slow_record_zero_pending_bits {h after : Heap} {r : ZStreamRef} {ds oo : Nat} {ref : BRef}
    {z : ZStream} {d result : DeflateState} {before : List Bool}
    (goodA : DGood after r ds z result) (buffersA : StreamBuffers after r)
    (frame : SlowRecordFrame d result) (pointer : z.next_out = .ref ref oo)
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
  have bytesA := caller_empty_output_view goodA.live.hz buffersA pointer
  exact ⟨bytesA, bitsA⟩

/-- The actual nonfull deferred-literal decision extends the symbol
ledger and preserves every held bit. Both caller-output return branches
retain the same content and EOF frontiers, including short input. -/
theorem default_foreign_slow_literal_nonfull_search_encoding {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
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
  obtain ⟨bytesA, bitsA⟩ := generic_slow_record_zero_pending_bits boundaryA.good buffersA frame pointer pending cursor pendingBefore
  have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, bits⟩) frame
  exact ⟨after, result, Zlib.Trees.Proofs.Out.outBits buf d, run, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, pendingBefore, bytesA, bitsA⟩

/-- The actual no-symbol defer branch advances one byte without changing
any output bit. Its pending input credit, both chain frontiers and caller
ranges are the actual returned state, including at the last input byte. -/
theorem default_foreign_slow_defer_search_encoding {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
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
  obtain ⟨bytesA, bitsA⟩ := generic_slow_record_zero_pending_bits boundaryA.good buffersA frame pointer pending cursor pendingBefore
  have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, bits⟩) frame
  exact ⟨after, result, Zlib.Trees.Proofs.Out.outBits buf d, run, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, pendingBefore, bytesA, bitsA⟩


theorem default_foreign_slow_match_nonfull_search_encoding {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (nonfull : (d.sym_next + 3 == d.sym_end) = false)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ head after result before,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ({ st with hash_head := head, bflush := false }, after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [emittedMatch d]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z 0 0 ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ PublishReady result ∧
      PendingBits h d before ∧ Bytes after z.next_out 0 [] ∧ PendingBits after result before := by
  obtain ⟨head, after, result, emitRun, boundaryA, endA, buffersA, frame,
      _available, startA, lookA, endpoint, countA, endCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict hash_head
  have room := literal_room cut.good.inv strict
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := cut.symbols
  have exactCount : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have notEqual : d.sym_next.toNat + 3 ≠ d.sym_end.toNat := by
    intro equal
    have machine : d.sym_next + 3 = d.sym_end := UInt32.toNat_inj.mp (exactCount.trans equal)
    simp only [machine, beq_self_eq_true] at nonfull
    cases nonfull
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by rw [countA, endCount]; omega
  have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, bits⟩) frame
  have beforeBits := pending_bits_base trees cursor
  obtain ⟨pbA, bufA, treesA, _ledgerA, _balanceA⟩ := boundaryA.symbols
  have cursorA : result.pending_out = result.pending_buf := by rw [frame]; exact cursor
  have zeroA : result.pending = 0 := by rw [frame]; exact pending
  have afterBits := pending_bits_base treesA cursorA
  have sameBits : Zlib.Trees.Proofs.Out.outBits bufA result = Zlib.Trees.Proofs.Out.outBits buf d := by
    rw [pending_bits_zero_value zeroA afterBits, pending_bits_zero_value pending beforeBits]
    rw [frame]
  rw [sameBits] at afterBits
  have bytesA := caller_empty_output_view boundaryA.good.live.hz buffersA pointer
  refine ⟨head, after, result, Zlib.Trees.Proofs.Out.outBits buf d, ?_, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, beforeBits, bytesA, afterBits⟩
  rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
  simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]

end Zlib.Deflate.Engine.Proofs
