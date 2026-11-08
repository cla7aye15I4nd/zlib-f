import ZlibF.Proof.«deflate.c.engine.match-full-prefix»
import ZlibF.Proof.«deflate.c.engine.literal-full-prefix»
import ZlibF.Proof.«deflate.c.engine.match-search-encoding»
import ZlibF.Proof.«deflate.c.engine.literal-full-encoding»
import ZlibF.Proof.«deflate.c.engine.nonpublishing-decision-encoding»
import ZlibF.Proof.«deflate.c.engine.short-decisions»

/-! # Every actual slow decision retains independently decoded output and its loop result -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Every actual slow decision retains either its held bits unchanged or
a completed, composable block prefix and the exact next bit-position
residue. Actual state guards and actual block costs select all branches.
No stored suffix alignment is left as a premise. Both loop frontiers and
control/rank facts belong to the same returned DecisionResult. -/
theorem slow_decision_all_search_block_prefix {h : Heap} {r : ZStreamRef} {ds w ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    ∃ decision : DecisionResult h r ds z d input origin base flush st head,
      ∃ before written remaining,
        PendingBits h d before ∧ written.length = decision.produced ∧
        Bytes decision.after z.next_out decision.produced written ∧ PendingBits decision.after decision.state remaining ∧
        ((decision.blockBase = base ∧ decision.produced = 0 ∧ written = [] ∧ remaining = before ∧
          decision.next.bflush = false) ∨
         (decision.symbols = [] ∧ decision.next.bflush = true ∧
          ∃ blockBits, ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
            BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix input decision.blockBase) ∧
            (offset + blockBits.length) % 8 = decision.state.bi_valid.toInt.toNat % 8)) := by
  have encoded : ∃ produced next after z' result base' ys before written remaining,
      slowDecision (some (.tab ds)) flush st head h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ written.length = produced ∧
      BlockInit.BlockClear result ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ((base' = base ∧ produced = 0 ∧ written = [] ∧ remaining = before ∧ next.bflush = false) ∨
       (ys = [] ∧ next.bflush = true ∧
        ∃ blockBits, ZlibF.Spec.bytesToBits written ++ remaining = before ++ blockBits ∧
          BlockPrefix [] offset (inputPrefix input base) blockBits (inputPrefix input base') ∧
          (offset + blockBits.length) % 8 = result.bi_valid.toInt.toNat % 8)) := by
    by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
    · by_cases full : (d.sym_next + 3 == d.sym_end) = true
      · obtain ⟨produced, nextHead, after, z', result, before, written, remaining, kind, body,
          run, boundaryA, endA, buffersA, accountA, clearA, _startA, _lookA, _endpoint,
          strictA, configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter, _kindA,
          wire, prefixA, nextPosition⟩ :=
          slow_match_full_search_block_prefix cut buffers selected strict full positive pointer cursor memory pending
            (by omega) clear position flush st head
        let next := if z'.avail_out == 0 then
            { st with hash_head := nextHead, bflush := true, ret := some need_more }
          else { st with hash_head := nextHead, bflush := true }
        refine ⟨produced, next, after, z', result, base + represented (xs ++ [emittedMatch d]), [],
          before, written, remaining, run, boundaryA, endA, buffersA, accountA,
          public_bytes_length bytesA, clearA, strictA, Nat.le_add_right _ _, configA,
          lowA, phaseA, pendingBefore, bytesA, pendingAfter, Or.inr ⟨rfl, ?_,
          Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body,
          wire, prefixA, ?_⟩⟩
        · dsimp only [next]; split <;> rfl
        · have count : (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body).length = 3 + body.length := by
            simp only [List.length_append, Zlib.Trees.Proofs.Out.natBits_length]
          rw [count]
          simpa only [Nat.add_assoc] using nextPosition
      · obtain ⟨produced, nextHead, after, z', result, base', ys, before, written, remaining,
          run, boundaryA, endA, buffersA, accountA, length, clearA, _startA, _lookA,
          _endpoint, strictA, baseLe, configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter, casesA⟩ :=
          slow_match_search_encoding cut buffers selected strict positive pointer cursor memory pending bits clear flush st head
        let next := if d.sym_next + 3 == d.sym_end then
            if z'.avail_out == 0 then { st with hash_head := nextHead, bflush := true, ret := some need_more }
            else { st with hash_head := nextHead, bflush := true }
          else { st with hash_head := nextHead, bflush := false }
        refine ⟨produced, next, after, z', result, base', ys, before, written, remaining,
          run, boundaryA, endA, buffersA, accountA, length, clearA, strictA, baseLe,
          configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter, ?_⟩
        rcases casesA with nonfull | published
        · obtain ⟨flag, _sameZ, zero, empty, remainingEq, baseEq, _symbols⟩ := nonfull
          exact Or.inl ⟨baseEq, zero, empty, remainingEq, by simp only [next, flag, Bool.false_eq_true, ite_false]⟩
        · exact (full published.1).elim
    · have branch := Bool.eq_false_iff.mpr selected
      by_cases available : d.match_available = 0
      · obtain ⟨after, result, before, run, boundaryA, endA, buffersA, accountA, clearA,
          _startA, _lookA, _endpoint, strictA, configA, lowA, readyA, pendingBefore, bytesA, pendingAfter⟩ :=
          slow_defer_search_encoding cut buffers lookahead branch available strict pointer cursor pending bits clear flush st head
        exact ⟨0, { st with hash_head := head, bflush := false }, after, z, result, base, xs, before, [], before,
          run, boundaryA, endA, buffersA, accountA, rfl, clearA, strictA, Nat.le_refl _, configA,
          lowA, fun _ => readyA, pendingBefore, bytesA, pendingAfter, Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      · have room := literal_room cut.good.inv strict
        by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
        · obtain ⟨produced, after, z', result, before, written, remaining, kind, body,
            run, boundaryA, endA, buffersA, accountA, length, clearA, _startA, _lookA,
            _endpoint, strictA, configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter,
            _kindBound, wire, prefixA, nextPosition⟩ :=
            slow_literal_full_search_block_prefix cut buffers lookahead branch available full positive pointer cursor memory pending
              bits clear position flush st head
          let next := if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
            else { st with hash_head := head, bflush := true }
          refine ⟨produced, next, after, z', result, base + represented (xs ++ [emittedLiteral d wa]), [],
            before, written, remaining, run, boundaryA, endA, buffersA, accountA, length,
            clearA, strictA, Nat.le_add_right _ _, configA, lowA, phaseA, pendingBefore,
            bytesA, pendingAfter, Or.inr ⟨rfl, ?_,
              Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body,
              wire, prefixA, ?_⟩⟩
          · dsimp only [next]; split <;> rfl
          · have count : (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body).length = 3 + body.length := by
              simp only [List.length_append, Zlib.Trees.Proofs.Out.natBits_length]
            rw [count]
            simpa only [Nat.add_assoc] using nextPosition
        · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
          obtain ⟨after, result, before, run, boundaryA, endA, buffersA, accountA,
              clearA, _startA, _lookA, _endpoint, strictA, configA, lowA, readyA,
              pendingBefore, bytesA, pendingAfter⟩ :=
            slow_literal_nonfull_search_encoding cut buffers lookahead branch available space pointer cursor pending bits clear flush st head
          let next := if z.avail_out == 0 then { st with hash_head := head, bflush := false, ret := some need_more }
            else { st with hash_head := head, bflush := false }
          refine ⟨0, next, after, z, result, base, xs ++ [emittedLiteral d wa], before, [], before,
            run, boundaryA, endA, buffersA, accountA, rfl, clearA, strictA, Nat.le_refl _,
            configA, lowA, fun _ => readyA, pendingBefore, bytesA, pendingAfter,
            Or.inl ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
          dsimp only [next]
          split <;> rfl
  obtain ⟨produced, next, after, z', result, base', ys, before, written, remaining,
    run, boundaryA, endA, buffersA, accountA, length, clearA, strictA, baseLe,
    configA, lowA, phaseA, pendingBefore, bytesA, pendingAfter, casesA⟩ := encoded
  obtain ⟨old⟩ := slow_decision_all_search_boundary cut buffers lookahead strict positive pointer cursor memory pending
    (by omega) clear flush st head
  have pair := Prod.mk.inj (Except.ok.inj (old.run.symm.trans run))
  have oldBoundary := old.boundary
  rw [pair.2] at oldBoundary
  have streams : old.stream = z' := Option.some.inj (oldBoundary.good.live.hz.symm.trans boundaryA.good.live.hz)
  have states : old.state = result := Option.some.inj (oldBoundary.good.live.hs.symm.trans boundaryA.good.live.hs)
  have progress : d.strstart.toNat < result.strstart.toNat := by rw [← states]; exact old.progress
  have less : result.lookahead.toNat < d.lookahead.toNat := by rw [← states]; exact old.less
  have endpoint : fillEnd result = fillEnd d := by rw [← states]; exact old.endpoint
  have brk : next.brk = st.brk := by rw [← pair.1]; exact old.brk
  have returns : next.ret = st.ret ∨ next.ret = some need_more := by rw [← pair.1]; exact old.returns
  have reason : next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0 := by
    simpa only [pair.1, streams] using old.reason
  have continues : 0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat := by
    simpa only [pair.1, streams] using old.continues
  refine ⟨⟨produced, next, after, z', result, base', ys, run, boundaryA, endA,
    buffersA, accountA, clearA, configA, lowA, phaseA, strictA, progress, less, endpoint,
    baseLe, brk, returns, reason, continues⟩, before, written, remaining,
    pendingBefore, length, bytesA, pendingAfter, ?_⟩
  exact casesA

end Zlib.Deflate.Engine.Proofs
