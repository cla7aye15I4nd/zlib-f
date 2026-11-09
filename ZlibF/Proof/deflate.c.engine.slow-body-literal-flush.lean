import ZlibF.Proof.«deflate.c.borrow-stable-private-search»
import ZlibF.Proof.«deflate.c.engine.slow-literal-flush»

/-! # A complete slow iteration reaches and survives a full literal flush -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real complete body, including actual insertion and longest-match
search, preserves the initialized content boundary through a full literal
flush. This internal case has incoming match_length=2, a deferred byte,
ready lookahead and a symbol count one slot before full. The previous
length is therefore too short to select match emission, regardless of
the actual search result. The other full-buffer cases remain separate. -/
theorem slow_body_literal_full_flush {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (length : d.match_length = 2)
    (available : d.match_available ≠ 0) (lookahead : 262 ≤ d.lookahead.toNat)
    (full : d.sym_next.toNat + 3 = d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs + 1) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      next.brk = st.brk ∧ next.bflush = true ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (z'.avail_out = 0 → next.ret = some need_more) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have windowEq : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have arrayEq : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨key, found, pos, len, search, goodF, chainsF, lengthF, quality, bytesF, formF, storageF⟩ :=
    slow_search_boundary_storage boundary.good env chains (Nat.le_refl _) boundary.range lookahead
      boundary.history.1 (form (by omega))
  let df := matchState (lazyPrepare { d with ins_h := key }) pos len
  let candidate := (wfn qa key.toNat).toUInt32
  have branch : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = false := by
    have previous : df.prev_length = 2 := length
    simp only [previous, show ((2 : UInt32) ≥ MIN_MATCH_u) = False from by decide,
      decide_false, Bool.false_and]
  have ownedF := stream_owned_keys boundary.good goodF rfl rfl rfl rfl
  have buffersF := stream_buffers_private_read boundary.good.live.hz goodF.live.hz buffers storageF
    (fun b equal => (stream_owned_deflate boundary.good b).mpr (Or.inl equal)) ownedF (stream_accounting_zero z)
    (Zlib.Deflate.BorrowProofs.Private.stable_slowSearch _ _ _ _ search)
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  have getB : found.bytes pb = some buf := by rw [bytesF]; exact trees.base.bytes
  have treesF := trees_at_buffer goodF trees.base.pbuf getB
  have getF : found.bytes w = some wa := by rw [bytesF]; exact env.wbytes
  have ledgerF : SymbolLedger buf df xs := ledger.keep rfl rfl rfl rfl
  have balanceF : BlockBalance df xs 1 := by
    change BlockBalance d xs 1
    simpa only [deferredCredit, available, ite_false] using balance
  have accountF : base + represented xs + 1 = origin + df.strstart.toNat := by
    change base + represented xs + 1 = origin + d.strstart.toNat
    simpa only [pendingCredit, available, ite_false] using boundary.accounted
  have clearF : BlockInit.BlockClear df := clear.slow (show SlowRecordFrame d df from rfl)
  have matching : 3 ≤ df.match_length.toNat →
      GoodMatch wa df.strstart.toNat df.w_size.toNat df.match_start.toNat df.match_length.toNat := by
    intro large
    have improved : d.match_length.toNat < len.toNat := by rw [length]; change 2 < len.toNat; exact Nat.lt_of_lt_of_le (by decide) large
    exact quality large improved
  have current : WindowLazyHistory (advanceOne df) wa :=
    window_lazy_history_advance goodF.inv boundary.range lookahead lengthF available matching
  have counts := advance_one_counts goodF.inv boundary.range (by change 1 ≤ d.lookahead.toNat; omega)
  have historyF : LazyHistory input origin (advanceOne df) := window_history_logical current (by
    intro i fit
    rw [counts.2.2] at fit
    exact view i fit)
  obtain ⟨produced, after, z', result, decision, boundaryA, buffersA, accountA, clearA, startA, lookA, endpoint⟩ :=
    slow_literal_full_flush_content goodF treesF buffersF chainsF positive pointer cursor memory pending bits
      ledgerF clearF boundary.trace env.win getF boundary.range (by change 1 ≤ d.lookahead.toNat; omega)
      (boundary.deferred available) balanceF accountF view branch available full flush st candidate
      (boundary.ready (by omega)) historyF formF
  let next : LoopS := if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
    else { st with hash_head := candidate, bflush := true }
  refine ⟨produced, next, after, z', result, ?_, ?_, buffersA, accountA, clearA, startA, lookA, endpoint,
    ?_, ?_, ?_, ?_⟩
  · have enough : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
      rw [UInt32.lt_iff_toNat_lt]
      change ¬ d.lookahead.toNat < 262
      omega
    rw [slow_body_source]
    simp only [bind_app, rdD_eq, boundary.good.live.hs, enough, ite_false, search]
    exact decision
  · change ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedLiteral df wa])) [] at boundaryA
    rw [represented_snoc, show (emittedLiteral df wa).bytes = 1 from rfl] at boundaryA
    simpa only [Nat.add_assoc] using boundaryA
  · dsimp only [next]; split <;> rfl
  · dsimp only [next]; split <;> rfl
  · dsimp only [next]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro empty
    simp only [next, empty, BEq.rfl, ite_true]

end Zlib.Deflate.Engine.Proofs
