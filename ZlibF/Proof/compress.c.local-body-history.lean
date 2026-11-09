import ZlibF.Proof.«compress.c.local-match-symbols»
import ZlibF.Proof.«compress.c.local-search»

/-! # Logical matching history across all three actual ordinary decisions -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalBodyHistory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral ZlibF.Spec.Public.Proofs.CompressLocalSearch
open ZlibF.Spec.Public.Proofs.CompressLocalMatchSymbols
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The actual deferred-byte scalar update preserves local storage. -/
theorem local_defer_one {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat}
    {z : ZStream} {d : DeflateState}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    LocalState (setD h ds (deferOne d)) cutoff r ds z (deferOne d) ∧
      HeapChains (setD h ds (deferOne d)) (deferOne d) top ∧
      (deferOne d).strstart.toNat + (deferOne d).lookahead.toNat ≤ (deferOne d).window_size.toNat := by
  have advanced := local_advance_one good chains range positive
  have inv : DStInv h ds (deferOne d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨local_state_setD good (d' := deferOne d) rfl good.live.status inv (by trkeep), ?_, advanced.2.2⟩
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := advanced.2.1
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

theorem local_defer_symbols {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := candidate, bflush := false }, setD h ds (deferOne d)) ∧
    SymbolBoundary (setD h ds (deferOne d)) ds (deferOne d) xs ∧ SlowRecordFrame d (deferOne d) := by
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have credit : deferredCredit d = 0 := by simp [deferredCredit, available]
  rw [credit] at balance
  have goodA := (local_defer_one good chains range positive).1
  have ledgerA : SymbolLedger buf (deferOne d) xs := ledger.keep rfl rfl rfl rfl
  have creditA : deferredCredit (deferOne d) = 1 := by simp [deferredCredit, deferOne]
  have balanceA : BlockBalance (deferOne d) xs (deferredCredit (deferOne d)) := by
    rw [creditA]
    exact balance_advance_one good.inv range positive balance
  exact ⟨slow_defer_branch good.live.hs branch available flush st candidate,
    local_symbol_boundary_of_ledger goodA trees.base.pbuf trees.base.bytes ledgerA balanceA, rfl⟩

/-- The whole real ordinary body preserves logical input matching across
defer, literal and selected-match decisions, including its exact emitted
symbol and deferred-byte credit. The logical history and window view are
internal invariants, to be supplied by actual initialization/refill and
preserved by execution; they are not public caller assumptions. This is
an ordinary nonfull-symbol-buffer step, not the full utility theorem. -/
theorem local_body_history_symbols {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
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
      LocalState after cutoff r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      LazyHistory input origin result ∧ DeferredByte result ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      SymbolBoundary after ds result ys ∧ SlowSymbolStep d wa xs ys ∧ SlowRecordFrame d result ∧
      SlowSymbolValueStep d wa xs ys ∧ ByteFrame h after (DeflateOwned ds d) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z.avail_out = 0) := by
  obtain ⟨key, found, pos, len, search, goodF, chainsF, lengthF, _clippedF, quality, bytesF, formF, searchFrameHeap,
      _shapeF,_fullF,_liveF,_allocF,_nextF⟩ :=
    local_slow_search_room good env chains ordered range (by omega) (by omega) history.1 form
  let df := matchState (lazyPrepare { d with ins_h := key }) pos len
  let candidate := (wfn qa key.toNat).toUInt32
  have searchFrame : SlowRecordFrame d df := rfl
  have searchStorage : ByteFrame h found (DeflateOwned ds d) :=
    searchFrameHeap.weaken (fun _ equal => Or.inl equal)
  have symbolF : SymbolBoundary found ds df xs := by
    obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
    have get : found.bytes b = some buf := by rw [bytesF]; exact trees.base.bytes
    have ledgerF : SymbolLedger buf df xs := ledger.keep rfl rfl rfl rfl
    have balanceF : BlockBalance df xs (deferredCredit df) := balance
    exact local_symbol_boundary_of_ledger goodF trees.base.pbuf get ledgerF balanceF
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
    simp only [bind_app, rdD_eq, good.live.hs, enough, ite_false, search]
    exact decision
  by_cases selected : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = true
  · obtain ⟨head, after, result, decision, goodA, chainsA, winA, bytesA, availableA, _, _, startA,
        lookA, endpoint, rangeA, formA, countA, historyA, symbolA, recordA, storageA⟩ :=
      local_match_symbol_storage goodF symbolF chainsF env.win getF prevF selected lookahead range formF space flush st candidate
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
      historyA, ?_, countA, rfl, Or.inl rfl, symbolA, Or.inr (Or.inr rfl), searchFrame.trans recordA, Or.inr (Or.inr ⟨previous, rfl⟩), searchStorage.trans storageA, fun returned => Or.inl returned⟩
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
      have kept := local_defer_one goodF chainsF range (by change 1 ≤ d.lookahead.toNat; omega)
      have current := window_lazy_history_defer goodF.inv range lookahead lengthF matching
      have endpoint : result.strstart.toNat + result.lookahead.toNat =
          d.strstart.toNat + d.lookahead.toNat := counts.2.2
      have historyA : LazyHistory input origin result := window_history_logical current (by
        intro i fit
        rw [endpoint] at fit
        exact view i fit)
      have ss : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
      have chainsA : HeapChains after result result.strstart.toNat := by rw [ss]; exact kept.2.1
      have symbolic := local_defer_symbols goodF symbolF chainsF range
        (by change 1 ≤ d.lookahead.toNat; omega) branch available flush st candidate
      refine ⟨{ st with hash_head := candidate, bflush := false }, after, result, xs,
        compose symbolic.1, kept.1,
        chainsA, env.win, getF, kept.2.2, endpoint, by rw [ss]; omega, ?_, ?_, historyA,
        ?_, ?_, rfl, Or.inl rfl, symbolic.2.1, Or.inl rfl, searchFrame.trans symbolic.2.2, Or.inl rfl,
        searchStorage.trans ((byte_frame_setD found ds result).weaken (fun _ equal => Or.inl equal)),
        fun returned => Or.inl returned⟩
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
      obtain ⟨after, decision, goodA, chainsA, rangeA, bytesA, countA, symbolA, recordA, storageA⟩ :=
        local_slow_literal_symbol_storage goodF symbolF chainsF env.win getF range (by change 1 ≤ d.lookahead.toNat; omega)
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
        rangeA, endpoint, by rw [ss]; omega, ?_, ?_, historyA, ?_, countA, ?_, ?_, symbolA, Or.inr (Or.inl rfl), searchFrame.trans recordA, Or.inr (Or.inl ⟨available, rfl⟩), searchStorage.trans storageA, ?_⟩
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
      · intro returned
        by_cases empty : z.avail_out = 0
        · exact Or.inr empty
        · left
          simpa [next, empty] using returned

end ZlibF.Spec.Public.Proofs.CompressLocalBodyHistory
