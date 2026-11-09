import ZlibF.Proof.«deflate.c.engine.flush-macro-size»
import ZlibF.Proof.«deflate.c.engine.decision-size-preserve»

/-! # The actual full match decision pays for one full symbol block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- At an actual full-buffer match decision, the newly completed block
represents at least 16383 bytes and costs at most that block's bytes plus
five. The real tally and match advance establish the zero-credit flush
entry. Caller publication may stop anywhere. Whole-loop counting remains
a separate induction over these actual steps. -/
theorem slow_match_full_counted_size {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (full : (d.sym_next + 3 == d.sym_end) = true)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (previous : PreviousShortQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    ∃ produced nextHead after z' result,
      slowDecision (some (.tab ds)) flush st head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := nextHead, bflush := true, ret := some need_more }
          else { st with hash_head := nextHead, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedMatch d])) [] ∧
      StreamAccounting z z' 0 produced ∧
      16383 ≤ represented (xs ++ [emittedMatch d]) ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + represented (xs ++ [emittedMatch d]) + 5 := by
  obtain ⟨answer, emittedHeap, emitted, emitRun, emittedBoundary, _emittedFrontier, emittedBuffers,
    emitFrame, emittedAvailable, _emittedStart, _emittedLook, _endpoint, emittedCount, emittedEnd, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict head
  obtain ⟨otherAnswer, otherHeap, other, otherRun, otherBoundary, _candidateE, floorE, qualityE⟩ :=
    slow_match_emit_size_facts cut buffers selected strict quality previous floor head
  have heapEq : otherHeap = emittedHeap := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans emitRun))).2
  rw [heapEq] at otherBoundary
  have stateEq : other = emitted := Option.some.inj (otherBoundary.good.live.hs.symm.trans emittedBoundary.good.live.hs)
  rw [stateEq] at floorE
  obtain ⟨pb, buf, trees, ledger, balance⟩ := emittedBoundary.symbols
  obtain ⟨sourceBlock, sourceWindow, win, get, view, _form⟩ := emittedBoundary.data
  have balance0 : BlockBalance emitted (xs ++ [emittedMatch d]) 0 := by
    simpa only [deferredCredit, emittedAvailable, ite_true] using balance
  have accounted0 : base + represented (xs ++ [emittedMatch d]) = origin + emitted.strstart.toNat := by
    simpa only [pendingCredit, emittedAvailable, ite_true, Nat.add_zero] using emittedBoundary.accounted
  have memoryE : emitted.lit_bufsize.toNat = 16384 := by rw [emitFrame]; exact memory
  have fullE : emitted.sym_next = emitted.sym_end := by
    apply UInt32.toNat_inj.mp
    obtain ⟨oldPb, oldBuf, oldTrees, _oldLedger, _oldBalance⟩ := cut.symbols
    have room := literal_room cut.good.inv strict
    have cast := literal_count oldTrees.base room 0
    change (d.sym_next + 3).toNat = d.sym_next.toNat + 3 at cast
    have exactWord : d.sym_next + 3 = d.sym_end := beq_iff_eq.mp full
    rw [exactWord] at cast
    rw [emittedCount, emittedEnd, cast]
  have large := full_ledger_represented_min trees ledger memoryE fullE
  obtain ⟨produced, after, z', result, macroRun, boundaryA, _buffersA, accountA, _clearA, _frameA⟩ :=
    flush_block_only_content_boundary emittedBoundary emittedBuffers (by rw [emitFrame]; exact positive)
      pointer (by rw [emitFrame]; exact cursor) memoryE (by rw [emitFrame]; exact pending)
      (by rw [emitFrame]; exact bits) (clear.slow emitFrame) emittedAvailable false
  have cost := flush_macro_run_byte_count emittedBoundary.good trees emittedBuffers
    (by rw [emitFrame]; exact positive) pointer (by rw [emitFrame]; exact cursor) memoryE
    (by rw [emitFrame]; exact strategy) (by rw [emitFrame]; exact pending) (by rw [emitFrame]; exact bits)
    ledger (clear.slow emitFrame) emittedBoundary.trace qualityE floorE win get emittedBoundary.range
    balance0 accounted0 view false macroRun boundaryA.good.live.hs boundaryA.good.live.hz accountA
  rw [outBits_length] at cost
  have pendingE : emitted.pending = 0 := by rw [emitFrame]; exact pending
  have bitsE : emitted.bi_valid = d.bi_valid := by rw [emitFrame]
  rw [pendingE, UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add, bitsE] at cost
  refine ⟨produced, answer, after, z', result, ?_, boundaryA, accountA, large, cost⟩
  change FLUSH_BLOCK_ONLY (some (.tab ds)) 0 emittedHeap = .ok ((), after) at macroRun
  have flushRun : FLUSH_BLOCK (some (.tab ds)) 0 emittedHeap =
      .ok ((if z'.avail_out == 0 then some need_more else none), after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, macroRun, ldDeflateState_tab boundaryA.good.live.hs,
      boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  rw [slow_decision_match_source cut.good.live.hs selected flush st head]
  simp only [bind_app, emitRun, full, ite_true, flushRun]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
