import ZlibF.Proof.«deflate.c.engine.strategy-encoding-cut»
import ZlibF.Proof.«deflate.c.engine.short-match-decision»
import ZlibF.Proof.«deflate.c.engine.public-output-bytes»

/-! # A real nonfull match decision preserves the entire unflushed bit prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real tally and match consumption add the selected symbol to the
input ledger without publishing or changing any output bits. Covers the
short insertion path and retains both loop frontiers. -/
theorem slow_match_nonfull_search_encoding {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (nonfull : (d.sym_next + 3 == d.sym_end) = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
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
  obtain ⟨written, bytesA, length⟩ := accounted_output_bytes boundaryA.good.live.hz buffersA pointer (stream_accounting_zero z)
  have emptyWritten : written = [] := by
    cases written with
    | nil => rfl
    | cons _ _ => simp at length
  rw [emptyWritten] at bytesA
  refine ⟨head, after, result, Zlib.Trees.Proofs.Out.outBits buf d, ?_, boundaryA, endA,
    buffersA, stream_accounting_zero z, clear.slow frame, startA, lookA, endpoint,
    strictA, ConfigFrame.slow frame, readyA.2.2, readyA, beforeBits, bytesA, afterBits⟩
  rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
  simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]

end Zlib.Deflate.Engine.Proofs
