import ZlibF.Proof.«deflate.c.engine.generic-foreign-decision-all»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual slow decision joins its real control and independently generated foreign-output encoding. -/
theorem default_foreign_slow_decision_all_search_encoding {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    ∃ decision : DecisionResult h r ds z d input origin base flush st head,
      ∃ before written remaining,
        PendingBits h d before ∧ written.length = decision.produced ∧
        Bytes decision.after z.next_out decision.produced written ∧ PendingBits decision.after decision.state remaining ∧
        ((decision.blockBase = base ∧ decision.produced = 0 ∧ written = [] ∧ remaining = before ∧
          decision.next.bflush = false) ∨
         (decision.symbols = [] ∧ decision.next.bflush = true ∧
          ∃ kind body, kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
            (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
            ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
              ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
                (inputPrefix input decision.blockBase))) := by
  have encoded : ∃ produced next after z' result base' ys before written remaining,
      slowDecision (some (.tab ds)) flush st head h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ written.length = produced ∧
      BlockInit.BlockClear result ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ((base' = base ∧ produced = 0 ∧ written = [] ∧ remaining = before ∧ next.bflush = false) ∨
       (ys = [] ∧ next.bflush = true ∧
        ∃ kind body, kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
          (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
          ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
            ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix (inputPrefix input base'))) := by
    by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
    · by_cases full : (d.sym_next + 3 == d.sym_end) = true
      · obtain ⟨produced, nextHead, after, z', result, before, written, remaining, kind, body,
            run, boundaryA, endA, buffersA, accountA, clearA, configA, _startA, _lookA,
            _endpoint, strictA, _smallA, lowA, phaseA, _cursorA, pendingBefore, bytesA,
            pendingAfter, kindBound, wire, grammar⟩ :=
          default_foreign_slow_match_full_encoding cut buffers selected strict full positive pointer memory ⟨pending, cursor, bits⟩ clear comparisonRoom flush st head
        let next := if z'.avail_out == 0 then
            { st with hash_head := nextHead, bflush := true, ret := some need_more }
          else { st with hash_head := nextHead, bflush := true }
        refine ⟨produced, next, after, z', result, base + represented (xs ++ [emittedMatch d]), [],
          before, written, remaining, run, boundaryA, endA, buffersA, accountA,
          public_bytes_length bytesA, clearA, strictA, Nat.le_add_right _ _, configA,
          lowA, phaseA, pendingBefore, bytesA, pendingAfter, Or.inr ⟨rfl, ?_,
          kind, body, kindBound, wire, grammar⟩⟩
        dsimp only [next]; split <;> rfl
      · have nonfull : (d.sym_next + 3 == d.sym_end) = false := Bool.eq_false_iff.mpr full
        obtain ⟨nextHead, after, result, before, run, boundaryA, endA, buffersA, accountA,
            clearA, _startA, _lookA, _endpoint, strictA, configA, lowA, readyA,
            pendingBefore, bytesA, pendingAfter⟩ :=
          default_foreign_slow_match_nonfull_search_encoding cut buffers selected strict nonfull pointer cursor pending bits clear flush st head
        exact ⟨0, { st with hash_head := nextHead, bflush := false }, after, z, result, base,
          xs ++ [emittedMatch d], before, [], before, run, boundaryA, endA, buffersA,
          accountA, rfl, clearA, strictA, Nat.le_refl _, configA, lowA,
          fun _ => readyA, pendingBefore, bytesA, pendingAfter,
          Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · have branch := Bool.eq_false_iff.mpr selected
      by_cases available : d.match_available = 0
      · obtain ⟨after, result, before, run, boundaryA, endA, buffersA, accountA, clearA,
          _startA, _lookA, _endpoint, strictA, configA, lowA, readyA, pendingBefore, bytesA, pendingAfter⟩ :=
          default_foreign_slow_defer_search_encoding cut buffers lookahead branch available strict pointer cursor pending bits clear flush st head
        exact ⟨0, { st with hash_head := head, bflush := false }, after, z, result, base, xs, before, [], before,
          run, boundaryA, endA, buffersA, accountA, rfl, clearA, strictA, Nat.le_refl _, configA,
          lowA, fun _ => readyA, pendingBefore, bytesA, pendingAfter, Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      · have room := literal_room cut.good.inv strict
        by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
        · obtain ⟨produced, after, z', result, before, written, remaining, kind, body,
            run, boundaryA, endA, buffersA, accountA, clearA, _startA, _lookA,
            _endpoint, strictA, configA, lowA, phaseA, _cursorA, _smallA, pendingBefore, bytesA, pendingAfter,
            kindBound, wire, grammar⟩ :=
            default_foreign_slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer cursor
              memory comparisonRoom pending (by omega) clear flush st head
          let next := if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
            else { st with hash_head := head, bflush := true }
          refine ⟨produced, next, after, z', result, base + represented (xs ++ [emittedLiteral d wa]), [],
            before, written, remaining, run, boundaryA, endA, buffersA, accountA, public_bytes_length bytesA,
            clearA, strictA, Nat.le_add_right _ _, configA, lowA, phaseA, pendingBefore,
            bytesA, pendingAfter, Or.inr ⟨rfl, ?_, kind, body, kindBound, wire, grammar⟩⟩
          dsimp only [next]
          split <;> rfl
        · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
          obtain ⟨after, result, before, run, boundaryA, endA, buffersA, accountA,
              clearA, _startA, _lookA, _endpoint, strictA, configA, lowA, readyA,
              pendingBefore, bytesA, pendingAfter⟩ :=
            default_foreign_slow_literal_nonfull_search_encoding cut buffers lookahead branch available space pointer cursor pending bits clear flush st head
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
  obtain ⟨old⟩ := default_foreign_slow_decision_all cut buffers lookahead strict positive pointer cursor memory comparisonRoom pending
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
