import ZlibF.Proof.«deflate.c.engine.flush-block-prefix»
import ZlibF.Proof.«deflate.c.engine.short-match-decision»

/-! # Actual full match decisions retain their independent block encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The actual full match decision returns a composable block prefix and
its next absolute bit-position residue, together with both loop frontiers.
Stored alignment is derived by the real flush. Short remaining input,
including the two-byte insertion path, and all capacities are covered. -/
theorem slow_match_full_search_block_prefix {h : Heap} {r : ZStreamRef} {ds w ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (full : (d.sym_next + 3 == d.sym_end) = true)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ produced head after z' result before written remaining kind body,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedMatch d])) [] ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      BlockPrefix [] offset (inputPrefix input base)
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body)
        (inputPrefix input (base + represented (xs ++ [emittedMatch d]))) ∧
      (offset + 3 + body.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier,
      emittedBuffers, emitFrame, emittedFlag, emittedStart, emittedLook, emittedEnd,
      _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict hash_head
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  obtain ⟨produced, after, z', result, beforeE, written, remaining, kind, body,
    flushRun, boundaryA, endA, buffersA, accountA, clearA, frameA, lowA, phaseA,
    pendingE, bytesA, pendingA, kindA, _storedA, nextPosition, outputA, prefixA⟩ :=
    flush_nonfinal_end_block_prefix (offset := offset) emittedBoundary emittedFrontier emittedBuffers
      (by rw [configE.level]; exact positive) pointer
      (by rw [emitFrame]; exact cursor) (by rw [configE.memory]; exact memory)
      (by rw [emitFrame]; exact pending) (by rw [emitFrame]; exact bits) clearE emittedFlag (by rw [emitFrame]; exact position)
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := cut.symbols
  have pendingEmitted : emitted.pending = 0 := by rw [emitFrame]; exact pending
  have valueE := pending_bits_zero_value pendingEmitted pendingE
  have wordE : emitted.bi_buf = d.bi_buf := by rw [emitFrame]
  have validE : emitted.bi_valid = d.bi_valid := by rw [emitFrame]
  rw [wordE, validE] at valueE
  have beforeOld : Zlib.Trees.Proofs.Out.outBits buf d =
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, pending]
  rw [← beforeOld] at valueE
  rw [valueE] at outputA
  have startA : result.strstart = emitted.strstart := by rw [frameA]
  have lookA : result.lookahead = emitted.lookahead := by rw [frameA]
  have endpoint : fillEnd result = fillEnd emitted := by rw [frameA]; rfl
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by
    obtain ⟨_, _, treesA, ledgerA, _⟩ := boundaryA.symbols
    have count := ledgerA.count
    have extent := treesA.base.sym_end
    have lower := treesA.base.lit_lo
    simp only [List.length_nil, Nat.mul_zero] at count
    omega
  refine ⟨produced, head, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d,
    written, remaining, kind, body, ?_, boundaryA, endA, buffersA, accountA, clearA,
    ?_, ?_, ?_, strictA, configE.trans (ConfigFrame.flush frameA), lowA, phaseA,
    pending_bits_base trees cursor, bytesA, pendingA, kindA, outputA, prefixA, nextPosition⟩
  · rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
    simp only [bind_app, emitRun, full, ite_true, flushRun]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  · rw [startA]; exact emittedStart
  · rw [lookA]; exact emittedLook
  · rw [endpoint]; exact emittedEnd

end Zlib.Deflate.Engine.Proofs
