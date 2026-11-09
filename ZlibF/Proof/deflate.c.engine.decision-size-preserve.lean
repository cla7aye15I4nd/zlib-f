import ZlibF.Proof.«deflate.c.engine.decision-size-history»
import ZlibF.Proof.«deflate.c.engine.short-decisions»

/-! # Every actual slow decision preserves its current block's cost facts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem packed_symbols_unique {buf : Array UInt8} {base : Nat} {xs ys : List Symbol}
    (left : PackedSymbols buf base xs) (right : PackedSymbols buf base ys)
    (validL : ∀ s ∈ xs, s.Valid) (validR : ∀ s ∈ ys, s.Valid) (length : xs.length = ys.length) : xs = ys := by
  apply List.ext_getElem length
  intro i leftFit rightFit
  have first := packed_payload_symbol left validL i xs[i] (List.getElem?_eq_getElem leftFit)
  have second := packed_payload_symbol right validR i ys[i] (List.getElem?_eq_getElem rightFit)
  have pair := Prod.mk.inj (first.symm.trans second)
  have injective (a b : Symbol) (distance : a.distance = b.distance) (value : a.value = b.value) : a = b := by
    cases a; cases b; simp_all
  exact injective _ _ pair.1 pair.2

theorem symbol_boundary_symbols_unique {h : Heap} {ds : Nat} {d : DeflateState} {xs ys : List Symbol}
    (left : SymbolBoundary h ds d xs) (right : SymbolBoundary h ds d ys) : xs = ys := by
  obtain ⟨leftId, leftBuf, leftTrees, leftLedger, _leftBalance⟩ := left
  obtain ⟨rightId, rightBuf, rightTrees, rightLedger, _rightBalance⟩ := right
  have sameId : leftId = rightId := by
    have same := leftTrees.base.pbuf.symm.trans rightTrees.base.pbuf
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using same
  subst rightId
  have sameBuf : leftBuf = rightBuf := Option.some.inj (leftTrees.base.bytes.symm.trans rightTrees.base.bytes)
  subst rightBuf
  exact packed_symbols_unique leftLedger.packed rightLedger.packed leftLedger.valid rightLedger.valid (by
    have first := leftLedger.count
    have second := rightLedger.count
    omega)

private theorem start_cast_nonnegative (position : UInt32) : 0 ≤ position.toUInt64.toInt64.toInt := by
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
  · omega
  · simp
    have := position.toNat_lt
    omega

private theorem reset_source_floor {before after : DeflateState} (position : UInt32)
    (frame : FlushWorkFrame { before with block_start := position.toUInt64.toInt64 } after) : StoredSourceFloor after := by
  intro negative
  rw [frame] at negative
  have positive := start_cast_nonnegative position
  change position.toUInt64.toInt64.toInt < 0 at negative
  omega

private theorem literal_quality_append (xs : List Symbol) (d : DeflateState) (wa : Array UInt8)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∀ s ∈ xs ++ [emittedLiteral d wa], s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
  intro s member nonzero zero
  rcases List.mem_append.mp member with old | fresh
  · exact quality s old nonzero zero
  · have same : s = emittedLiteral d wa := List.mem_singleton.mp fresh
    subst s
    exact False.elim (nonzero rfl)

/-- All actual selected-match, deferred-literal and defer decisions retain
the lazy quality, source floor and quality of the current symbol ledger.
Both full-buffer publications and every caller output capacity are covered.
The supplied run and returned ledger come from the existing actual decision
execution; this observer assumes no called-function specification. -/
theorem slow_decision_run_size_facts {h after : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {wa : Array UInt8} {xs ys : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {head : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (lookahead : 1 ≤ d.lookahead.toNat) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (fresh : FreshShortQuality d) (previous : PreviousShortQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : slowDecision (some (.tab ds)) flush st head h = .ok (next, after))
    (live : after.dstates ds = some result) (symbols : SymbolBoundary after ds result ys) :
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
  have known : ∃ computed answer state zs,
      slowDecision (some (.tab ds)) flush st head h = .ok (answer, computed) ∧
      computed.dstates ds = some state ∧ SymbolBoundary computed ds state zs ∧
      ShortCandidateQuality state ∧ StoredSourceFloor state ∧
      (∀ s ∈ zs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
    by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
    · obtain ⟨answer, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers,
        emitFrame, emittedAvailable, _emittedStart, _emittedLook, _endpoint, _count, _endCount, _storage⟩ :=
        slow_match_emit_search_boundary cut buffers selected strict head
      obtain ⟨otherAnswer, otherHeap, other, otherRun, otherBoundary, qualityE, floorE, symbolsE⟩ :=
        slow_match_emit_size_facts cut buffers selected strict quality previous floor head
      have heapEq : otherHeap = emittedHeap := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans emitRun))).2
      rw [heapEq] at otherBoundary
      have stateEq : other = emitted := Option.some.inj (otherBoundary.good.live.hs.symm.trans emittedBoundary.good.live.hs)
      rw [stateEq] at qualityE floorE
      by_cases full : (d.sym_next + 3 == d.sym_end) = true
      · obtain ⟨produced, computed, z', state, flushRun, boundaryA, _frontierA, _buffersA, _accountA,
          _clearA, frameA, _bitsA, _resumeA⟩ := flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
          (by rw [emitFrame]; exact positive) pointer (by rw [emitFrame]; exact cursor)
          (by rw [emitFrame]; exact memory) (by rw [emitFrame]; exact pending) (by rw [emitFrame]; exact bits)
          (clear.slow emitFrame) emittedAvailable
        let answer' := if z'.avail_out == 0 then
          { st with hash_head := answer, bflush := true, ret := some need_more }
          else { st with hash_head := answer, bflush := true }
        have run : slowDecision (some (.tab ds)) flush st head h = .ok (answer', computed) := by
          rw [slow_decision_match_source cut.good.live.hs selected flush st head]
          simp only [bind_app, emitRun, full, ite_true, flushRun]
          by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, answer', pure_app]
        refine ⟨computed, answer', state, [], run, boundaryA.good.live.hs, boundaryA.symbols, ?_,
          reset_source_floor emitted.strstart frameA, by simp⟩
        rw [frameA]
        exact qualityE
      · have notFull : (d.sym_next + 3 == d.sym_end) = false := Bool.eq_false_iff.mpr full
        refine ⟨emittedHeap, { st with hash_head := answer, bflush := false }, emitted,
          xs ++ [emittedMatch d], ?_, emittedBoundary.good.live.hs, emittedBoundary.symbols, qualityE, floorE, symbolsE⟩
        rw [slow_decision_match_source cut.good.live.hs selected flush st head]
        simp only [bind_app, emitRun, notFull, Bool.false_eq_true, ite_false, pure_app]
    · have branch := Bool.eq_false_iff.mpr selected
      by_cases available : d.match_available = 0
      · have result := slow_defer_symbol_boundary cut.good cut.symbols cut.chains cut.range lookahead branch available flush st head
        refine ⟨setD h ds (deferOne d), { st with hash_head := head, bflush := false }, deferOne d, xs,
          result.1, by simp, result.2.1, defer_short_candidate_quality d fresh, ?_, quality⟩
        intro negative
        have lower := floor negative
        have count := (advance_one_counts cut.good.inv cut.range lookahead).1
        change 32506 ≤ (d.strstart + 1).toNat
        change (d.strstart + 1).toNat = d.strstart.toNat + 1 at count
        omega
      · have room := literal_room cut.good.inv strict
        by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
        · obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
          have balance1 : BlockBalance d xs 1 := by simpa only [deferredCredit, available, ite_false] using balance
          have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
            simpa only [pendingCredit, available, ite_false] using cut.accounted
          obtain ⟨produced, computed, z', state, run, goodA, _buffersA, _account, _chainsA, _winA, _bytesA,
            _startA, _lookA, _endpoint, _countA, _clearA, symbolsA, frameA, _accountedA, _configA, _bitsA, _resumeA⟩ :=
            slow_literal_full_flush_loop cut.good trees buffers cut.chains positive pointer cursor memory pending bits ledger clear cut.trace
              cut.window cut.bytes cut.range lookahead (cut.deferred available) balance1 accounted cut.view branch available full flush st head
          refine ⟨computed, _, state, [], run, goodA.live.hs, symbolsA, ?_, reset_source_floor d.strstart frameA, by simp⟩
          rw [frameA]
          exact advance_short_candidate_quality d fresh
        · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
          obtain ⟨computed, run, goodA, _chainsA, _rangeA, _bytesA, _strictA, symbolsA, _frameA, _storageA⟩ :=
            slow_literal_symbol_storage cut.good cut.symbols cut.chains cut.window cut.bytes cut.range lookahead
              (cut.deferred available) branch available space flush st head
          refine ⟨computed, _, _, xs ++ [emittedLiteral d wa], run, goodA.live.hs, symbolsA,
            advance_short_candidate_quality _ fresh, ?_, literal_quality_append xs d wa quality⟩
          intro negative
          have lower := floor negative
          have count := (advance_one_counts cut.good.inv cut.range lookahead).1
          change 32506 ≤ (d.strstart + 1).toNat
          change (d.strstart + 1).toNat = d.strstart.toNat + 1 at count
          omega
  obtain ⟨computed, answer, state, zs, run, get, ledgerA, candidateA, floorA, qualityA⟩ := known
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).2
  rw [heaps] at get ledgerA
  have sameState : state = result := Option.some.inj (get.symm.trans live)
  rw [sameState] at ledgerA candidateA floorA
  have sameSymbols : zs = ys := symbol_boundary_symbols_unique ledgerA symbols
  rw [sameSymbols] at qualityA
  exact ⟨candidateA, floorA, qualityA⟩

end Zlib.Deflate.Engine.Proofs
