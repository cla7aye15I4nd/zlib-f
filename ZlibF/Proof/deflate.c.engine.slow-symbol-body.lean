import ZlibF.Proof.«deflate.c.engine.slow-body»
import ZlibF.Proof.«deflate.c.engine.slow-symbols»

/-! # The full slow body preserves the initialized symbol boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def retainedMatchSymbol (d : DeflateState) : Symbol :=
  ⟨(d.strstart - 1 - d.match_start).toNat, (d.match_length - MIN_MATCH_u).toNat⟩

/-- The source emits at most one symbol in a non-flushing iteration. -/
def SlowSymbolStep (d : DeflateState) (wa : Array UInt8) (xs ys : List Symbol) : Prop :=
  ys = xs ∨ ys = xs ++ [emittedLiteral d wa] ∨ ys = xs ++ [retainedMatchSymbol d]

set_option maxHeartbeats 3000000 in
/-- Actual search and all three decisions keep the initialized symbol
boundary. The emitted list and exact unchanged state fields are retained,
along with the window, chain and logical matching facts. The source path
requires sufficient lookahead and room for a non-full tally.
-/
theorem slow_body_with_symbols {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs)
    (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (history : LazyHistory input origin d) (deferred : DeferredByte d)
    (view : ∀ i, i < d.strstart.toNat + d.lookahead.toNat → bfn wa i = input (origin + i))
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ next after result ys,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      LazyHistory input origin result ∧ DeferredByte result ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      SymbolBoundary after ds result ys ∧ SlowSymbolStep d wa xs ys ∧ SlowRecordFrame d result := by
  obtain ⟨key, found, pos, len, search, goodF, chainsF, lengthF, quality, bytesF, formF⟩ :=
    slow_search_boundary good env chains ordered range lookahead history.1 form
  let df := matchState (lazyPrepare { d with ins_h := key }) pos len
  let candidate := (wfn qa key.toNat).toUInt32
  have searchFrame : SlowRecordFrame d df := rfl
  have symbolF : SymbolBoundary found ds df xs := by
    obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
    have get : found.bytes b = some buf := by rw [bytesF]; exact trees.base.bytes
    have ledgerF : SymbolLedger buf df xs := ledger.keep rfl rfl rfl rfl
    have balanceF : BlockBalance df xs (deferredCredit df) := balance
    exact symbol_boundary_of_ledger goodF trees.base.pbuf get ledgerF balanceF
  have getF : found.bytes w = some wa := by rw [bytesF]; exact env.wbytes
  have prevF : PreviousHistory input origin df := logical_prepare_history history key
  have deferredF : DeferredByte df := deferred
  have enough : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
    rw [UInt32.lt_iff_toNat_lt]
    change ¬ d.lookahead.toNat < 262
    omega
  have compose {next : LoopS} {after : Heap}
      (decision : slowDecision (some (.tab ds)) flush st candidate found = .ok (next, after)) :
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) := by
    rw [slow_body_source]
    simp only [bind_app, rdD_eq, good.live.hs, enough, if_false, search]
    exact decision
  by_cases selected : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = true
  · obtain ⟨head, after, result, decision, goodA, chainsA, winA, bytesA, availableA, _, _, startA,
        lookA, endpoint, rangeA, formA, countA, historyA, symbolA, recordA⟩ :=
      slow_match_symbol_boundary goodF symbolF chainsF env.win getF prevF selected lookahead range formF space flush st candidate
    have previous : 3 ≤ df.prev_length.toNat := by
      have guard := selected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      exact UInt32.le_iff_toNat_le.mp guard.1
    have consumed : d.strstart.toNat < result.strstart.toNat := by
      change result.strstart.toNat = d.strstart.toNat + (df.prev_length.toNat - 1) at startA
      omega
    have endpointA : result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := endpoint
    refine ⟨{ st with hash_head := head, bflush := false }, after, result, xs ++ [emittedMatch df],
      compose decision, goodA, chainsA, winA, bytesA, rangeA, endpointA, consumed, ?_, formA,
      historyA, ?_, countA, rfl, Or.inl rfl, symbolA, Or.inr (Or.inr rfl), searchFrame.trans recordA⟩
    · omega
    · intro available
      exact False.elim (available availableA)
  · have branch : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = false :=
      Bool.eq_false_iff.mpr selected
    have matching : 3 ≤ df.match_length.toNat →
        GoodMatch wa df.strstart.toNat df.w_size.toNat df.match_start.toNat df.match_length.toNat := by
      intro large
      have improved := literal_search_improves branch large
      exact quality large improved
    have counts := advance_one_counts goodF.inv range (by change 1 ≤ d.lookahead.toNat; omega)
    by_cases available : df.match_available = 0
    · let result := deferOne df
      let after := setD found ds result
      have kept := defer_one_good goodF chainsF range (by change 1 ≤ d.lookahead.toNat; omega)
      have current := window_lazy_history_defer goodF.inv range lookahead lengthF matching
      have endpoint : result.strstart.toNat + result.lookahead.toNat =
          d.strstart.toNat + d.lookahead.toNat := counts.2.2
      have historyA : LazyHistory input origin result := window_history_logical current (by
        intro i fit
        rw [endpoint] at fit
        exact view i fit)
      have ss : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
      have chainsA : HeapChains after result result.strstart.toNat := by rw [ss]; exact kept.2.1
      have symbolic := slow_defer_symbol_boundary goodF symbolF chainsF range
        (by change 1 ≤ d.lookahead.toNat; omega) branch available flush st candidate
      refine ⟨{ st with hash_head := candidate, bflush := false }, after, result, xs,
        compose symbolic.1, kept.1,
        chainsA, env.win, getF, kept.2.2, endpoint, by rw [ss]; omega, ?_, ?_, historyA,
        ?_, ?_, rfl, Or.inl rfl, symbolic.2.1, Or.inl rfl, searchFrame.trans symbolic.2.2⟩
      · have la : result.lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
        omega
      · change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat key
        rw [ss]
        exact formF
      · intro _
        rw [ss]
        omega
      · change d.sym_next.toNat < d.sym_end.toNat
        omega
    · let c := wa[df.strstart.toNat - 1]!
      let result := advanceOne (literalState df c)
      obtain ⟨after, decision, goodA, chainsA, rangeA, bytesA, countA, symbolA, recordA⟩ :=
        slow_literal_symbol_boundary goodF symbolF chainsF env.win getF range (by change 1 ≤ d.lookahead.toNat; omega)
          (deferredF available) branch available space flush st candidate
      have current0 : WindowLazyHistory (advanceOne df) wa :=
        window_lazy_history_advance goodF.inv range lookahead lengthF available matching
      have current : WindowLazyHistory result wa := current0
      have endpoint : result.strstart.toNat + result.lookahead.toNat =
          d.strstart.toNat + d.lookahead.toNat := counts.2.2
      have historyA : LazyHistory input origin result := window_history_logical current (by
        intro i fit
        rw [endpoint] at fit
        exact view i fit)
      have ss : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
      have chainsBoundary : HeapChains after result result.strstart.toNat := by rw [ss]; exact chainsA
      let next : LoopS := if z.avail_out == 0 then
        { st with hash_head := candidate, bflush := false, ret := some need_more }
        else { st with hash_head := candidate, bflush := false }
      refine ⟨next, after, result, xs ++ [emittedLiteral df wa], compose decision, goodA, chainsBoundary, env.win, bytesA,
        rangeA, endpoint, by rw [ss]; omega, ?_, ?_, historyA, ?_, countA, ?_, ?_, symbolA, Or.inr (Or.inl rfl), searchFrame.trans recordA⟩
      · have la : result.lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
        omega
      · change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat key
        rw [ss]
        exact formF
      · intro _
        rw [ss]
        omega
      · dsimp only [next]
        split <;> rfl
      · dsimp only [next]
        split
        · exact Or.inr rfl
        · exact Or.inl rfl

end Zlib.Deflate.Engine.Proofs
