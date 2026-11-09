import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.short-match-decision»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual full slow-match decision with default memory and legal foreign-depth caller output.
Tally and match advance precede real block selection and publication in source order. -/
theorem default_foreign_slow_match_full_encoding {h : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (full : (d.sym_next + 3 == d.sym_end) = true)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384)
    (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ produced head after z' result before written remaining kind body,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedMatch d])) [] ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ result.strstart.toNat < 65536 ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented (xs ++ [emittedMatch d]))) := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, emittedStart, emittedLook, emittedEnd, _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict hash_head
  have clearE := clear.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have readyE := ready.slow emitFrame
  have windowMax : d.window_size.toNat ≤ 65536 := by
    have power := Nat.pow_le_pow_right (n := 2) (by decide) cut.good.inv.wbits_hi
    rw [cut.good.inv.wsz, cut.good.inv.wsize]
    omega
  have startSmallE : emitted.strstart.toNat < 65536 := by
    have previous := cut.previous.1
    rw [emittedStart]
    omega
  have memoryE : emitted.lit_bufsize.toNat = 16384 := by
    rw [configE.memory]; exact memory
  obtain ⟨produced, after, z', result, beforeE, written, remaining, kind, body, padding,
      macroRun, contentA, frontierA, buffersA, accountA, clearA, fieldsA, lowA, phaseA, cursorA,
      pendingE, bytesA, pendingA, kindA, _padBound, padNone, _storedPad, outputA, grammarA⟩ :=
    default_foreign_flush_macro_content_encoding emittedBoundary emittedFrontier emittedBuffers
      (by rw [configE.level]; exact positive) pointer readyE.2.1 memoryE
      readyE.1 (by have bits := readyE.2.2; omega) clearE emittedFlag false
  have flushRun : FLUSH_BLOCK (some (.tab ds)) 0 emittedHeap =
      .ok ((if z'.avail_out == 0 then some need_more else none), after) := by
    have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 emittedHeap = .ok ((), after) := macroRun
    unfold FLUSH_BLOCK
    simp only [bind_app, run0, ldDeflateState_tab contentA.good.live.hs,
      contentA.good.live.back, zrd_eq, contentA.good.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  have startA : result.strstart = emitted.strstart := by rw [fieldsA]
  have lookA : result.lookahead = emitted.lookahead := by rw [fieldsA]
  have endA : fillEnd result = fillEnd emitted := by rw [fieldsA]; rfl
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by
    obtain ⟨_, _, treesA, ledgerA, _⟩ := contentA.symbols
    have count := ledgerA.count
    have extent := treesA.base.sym_end
    have lower := treesA.base.lit_lo
    simp only [List.length_nil, Nat.mul_zero] at count
    omega
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := cut.symbols
  have valueE := pending_bits_zero_value readyE.1 pendingE
  have wordE : emitted.bi_buf = d.bi_buf := by rw [emitFrame]
  have validE : emitted.bi_valid = d.bi_valid := by rw [emitFrame]
  rw [wordE, validE] at valueE
  have beforeOld : Zlib.Trees.Proofs.Out.outBits buf d =
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, ready.1]
  rw [← beforeOld] at valueE
  rw [valueE, padNone rfl, List.append_nil] at outputA
  refine ⟨produced, head, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d,
    written, remaining, kind, body, ?_, contentA, frontierA, buffersA, accountA, clearA,
    configE.trans (ConfigFrame.flush fieldsA), ?_, ?_, endA.trans emittedEnd, strictA, ?_,
    lowA, phaseA, cursorA, pending_bits_base trees ready.2.1, bytesA, pendingA, kindA, outputA, grammarA⟩
  · rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
    simp only [bind_app, emitRun, full, ite_true, flushRun]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  · rw [startA]; exact emittedStart
  · rw [lookA]; exact emittedLook
  · rw [startA]; exact startSmallE

end Zlib.Deflate.Engine.Proofs
