import ZlibF.Proof.«deflate.c.borrow-stable-private-search»
import ZlibF.Proof.«deflate.c.engine.short-defer-boundary»

/-! # Nonfull short literal decisions retain the initialized boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual nonfull literal decision keeps the older pending and EOF
frontiers. Current match bytes are clipped to real lookahead. Caller
input/output counters are unchanged in this non-publishing decision. -/
theorem slow_literal_search_boundary {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (positive : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ after result,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z.avail_out == 0 then { st with hash_head := candidate, bflush := false, ret := some need_more }
          else { st with hash_head := candidate, bflush := false }), after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [emittedLiteral d wa]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ SlowRecordFrame d result ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ByteFrame h after (DeflateOwned ds d) := by
  let c := wa[d.strstart.toNat - 1]!
  let result := advanceOne (literalState d c)
  obtain ⟨after, run, goodA, frontierA, rangeA, bytesA, countA, symbolsA, frameA, storage⟩ :=
    slow_literal_symbol_storage cut.good cut.symbols cut.frontier cut.window cut.bytes cut.range
      positive (cut.deferred available) branch available space flush st candidate
  obtain ⟨other, otherRun, _otherGood, endOther, _⟩ :=
    slow_literal_symbol_storage cut.good cut.symbols cut.end_frontier cut.window cut.bytes cut.range
      positive (cut.deferred available) branch available space flush st candidate
  have sameHeap : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [sameHeap] at endOther
  have counts := advance_one_counts cut.good.inv cut.range positive
  have startA : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
  have lookA : result.lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
  have endpoint : fillEnd result = fillEnd d := counts.2.2
  have insertA : result.insert = d.insert := rfl
  have frontierAt : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    simpa only [startA, insertA] using frontierA
  have chainsAt := heap_chains_raise frontierAt (Nat.sub_le _ _)
  have endA : EndFrontier after result := by
    unfold EndFrontier
    simpa only [startA, endpoint] using endOther
  have matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat := by
    intro large
    exact cut.matching large (literal_search_improves branch large)
  have current := window_lazy_history_advance_bounded cut.good.inv cut.range positive cut.length available cut.clipped matching
  have historyA : LazyHistory input origin result := window_history_logical current (by
    intro i fit
    change i < fillEnd result at fit
    rw [endpoint] at fit
    exact cut.view i fit)
  have owned := stream_owned_keys cut.good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read cut.good.live.hz goodA.live.hz buffers storage
    (fun k own => (stream_owned_deflate cut.good k).mpr own) owned (stream_accounting_zero z)
    (Zlib.Deflate.BorrowProofs.Private.stable_slowDecision _ _ _ _ _ _ _ run)
  have credit : pendingCredit d = 1 := by simp only [pendingCredit, available, ite_false]
  have accounted := cut.accounted
  rw [credit] at accounted
  have meaning := literal_input_meaning cut.deferred available cut.view
  have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← position] at meaning
  have traceA := cut.trace.snoc meaning
  refine ⟨after, result, run, ?_, endA, buffersA, frameA, startA, lookA, endpoint, countA, storage⟩
  refine ⟨⟨⟨goodA, chainsAt, rangeA, historyA, ?_, symbolsA, ?_⟩,
    ?_, frontierAt, ?_⟩, traceA, ?_⟩
  · intro _; rw [startA]; omega
  · refine ⟨w, wa, cut.window, bytesA, ?_, ?_⟩
    · intro i fit; rw [endpoint] at fit; exact cut.view i fit
    · intro enough
      change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat d.ins_h
      rw [startA]
      apply cut.primed
      change 3 ≤ result.lookahead.toNat at enough
      rw [lookA] at enough
      omega
  · rw [insertA, startA]
    have bound := cut.insert_le
    omega
  · intro enough
    rw [insertA]
    apply cut.ready
    change 3 ≤ result.lookahead.toNat at enough
    rw [lookA] at enough
    omega
  · have creditA : pendingCredit result = 1 := credit
    rw [represented_snoc, show (emittedLiteral d wa).bytes = 1 from rfl, creditA, startA]
    omega

end Zlib.Deflate.Engine.Proofs
