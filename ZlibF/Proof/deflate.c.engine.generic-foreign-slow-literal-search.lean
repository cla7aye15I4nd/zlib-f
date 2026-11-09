import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-content»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_literal_full_search_boundary {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ produced after z' result before written remaining kind body,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
          else { st with hash_head := candidate, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedLiteral d wa])) [] ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧ result.strstart.toNat < 65536 ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧ kind < 3 ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented (xs ++ [emittedLiteral d wa]))) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have balance1 : BlockBalance d xs 1 := by simpa only [deferredCredit, available, ite_false] using balance
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  have matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat := by
    intro large
    exact cut.matching large (literal_search_improves branch large)
  have current := window_lazy_history_advance_bounded cut.good.inv cut.range lookahead cut.length available cut.clipped matching
  have counts := advance_one_counts cut.good.inv cut.range lookahead
  have historyA : LazyHistory input origin (advanceOne d) := window_history_logical current (by
    intro i fit
    rw [counts.2.2] at fit
    exact cut.view i fit)
  obtain ⟨produced, after, z', result, written, remaining, kind, body, run, boundaryA, buffersA, accountA, clearA,
      startA, lookA, endpoint, configA, lowA, phaseA, cursorA, smallA, pendingBefore, bytesA, pendingAfter, kindBound, wire, grammar⟩ :=
    default_foreign_slow_literal_full_flush_bounded_content cut.good trees buffers cut.frontier positive pointer cursor memory comparisonRoom pending bits
      ledger clear cut.trace cut.window cut.bytes cut.range lookahead (cut.deferred available) balance1 accounted
      cut.view branch available full flush st candidate cut.insert_le cut.ready historyA cut.primed
  obtain ⟨otherProduced, otherHeap, otherZ, otherD, _written, _remaining, _kind, _body, otherRun, otherGood, _otherBuffers, _otherAccount,
      endOther, _otherWin, _otherBytes, _otherStart, _otherLook, _otherEndpoint, _rest⟩ :=
    default_foreign_slow_literal_full_flush_loop cut.good trees buffers cut.end_frontier positive pointer cursor memory comparisonRoom pending bits
      ledger clear cut.trace cut.window cut.bytes cut.range lookahead (cut.deferred available) balance1 accounted
      cut.view branch available full flush st candidate
  have heapEq : otherHeap = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heapEq] at otherGood endOther
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans boundaryA.good.live.hs)
  rw [stateEq] at endOther
  have endA : EndFrontier after result := by
    unfold EndFrontier
    simpa only [startA, endpoint] using endOther
  have strict : result.sym_next.toNat < result.sym_end.toNat := by
    obtain ⟨_, _, treesA, ledgerA, _⟩ := boundaryA.symbols
    have count := ledgerA.count
    have extent := treesA.base.sym_end
    have lower := treesA.base.lit_lo
    simp only [List.length_nil, Nat.mul_zero] at count
    omega
  exact ⟨produced, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d, written, remaining, kind, body, run, boundaryA, endA, buffersA, accountA, clearA,
    startA, lookA, endpoint, strict, configA, lowA, phaseA, cursorA, smallA, pendingBefore, bytesA, pendingAfter, kindBound, wire, grammar⟩

end Zlib.Deflate.Engine.Proofs
