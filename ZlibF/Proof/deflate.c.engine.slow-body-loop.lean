import ZlibF.Proof.«deflate.c.engine.slow-match-loop»
import ZlibF.Proof.«deflate.c.engine.slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.slow-caller-storage»

/-! # Every slow decision with one remaining symbol slot -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 3000000 in
/-- The complete actual ready-lookahead body covers every decision at
one remaining symbol slot: full match, full literal, or no emitted symbol.
Actual insertion/search choose the branch. No selected-encoder or branch
contract is assumed. The input/content boundary comes from default init.
Short lookahead and the outer strategy loop are separate obligations. -/
theorem slow_body_full_slot_loop {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (lookahead : 262 ≤ d.lookahead.toNat)
    (full : d.sym_next.toNat + 3 = d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
      (base' : Nat) (ys : List Symbol),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      ((base' = base ∧ ys = xs ∧ next.bflush = false) ∨ (ys = [] ∧ next.bflush = true)) ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have windowEq : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have arrayEq : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨key, found, pos, len, search, goodF, chainsF, lengthF, quality, bytesF, formF, storageF⟩ :=
    slow_search_boundary_storage boundary.good env chains (Nat.le_refl _) boundary.range lookahead
      boundary.history.1 (form (by omega))
  let df := matchState (lazyPrepare { d with ins_h := key }) pos len
  let candidate := (wfn qa key.toNat).toUInt32
  have searchFrame : SlowRecordFrame d df := rfl
  have ownedF := stream_owned_keys boundary.good goodF rfl rfl rfl rfl
  have buffersF := stream_buffers_private_read boundary.good.live.hz goodF.live.hz buffers storageF
    (fun b equal => (stream_owned_deflate boundary.good b).mpr (Or.inl equal)) ownedF (stream_accounting_zero z)
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  have getB : found.bytes pb = some buf := by rw [bytesF]; exact trees.base.bytes
  have treesF := trees_at_buffer goodF trees.base.pbuf getB
  have getF : found.bytes w = some wa := by rw [bytesF]; exact env.wbytes
  have ledgerF : SymbolLedger buf df xs := ledger.keep rfl rfl rfl rfl
  have symbolF : SymbolBoundary found ds df xs := ⟨pb, buf, treesF, ledgerF, balance⟩
  have previousHistory : PreviousHistory input origin df := logical_prepare_history boundary.history key
  have clearF := clear.slow searchFrame
  have insert : df.insert = 0 := boundary.ready (by omega)
  have compose {next : LoopS} {after : Heap}
      (decision : slowDecision (some (.tab ds)) flush st candidate found = .ok (next, after)) :
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) := by
    have enough : ¬ d.lookahead < MIN_LOOKAHEAD_u := by
      rw [UInt32.lt_iff_toNat_lt]
      change ¬ d.lookahead.toNat < 262
      omega
    rw [slow_body_source]
    simp only [bind_app, rdD_eq, boundary.good.live.hs, enough, ite_false, search]
    exact decision
  have fullNext {produced : Nat} {after : Heap} {z' : ZStream} {result : DeflateState} {nextBase : Nat}
      {head : UInt32} (decision : slowDecision (some (.tab ds)) flush st candidate found =
        .ok ((if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), after))
      (state : ContentBoundary after r ds z' result input origin nextBase [])
      (buffersA : StreamBuffers after r) (accountA : StreamAccounting z z' 0 produced)
      (clearA : BlockInit.BlockClear result)
      (progress : d.strstart.toNat < result.strstart.toNat)
      (less : result.lookahead.toNat < d.lookahead.toNat) (endpoint : fillEnd result = fillEnd d)
      (baseLe : base ≤ nextBase) (configA : ConfigFrame d result) (lowA : result.bi_valid.toInt < 8)
      (phaseA : 0 < z'.avail_out.toNat → PublishReady result) :
      ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
        (base' : Nat) (ys : List Symbol),
        deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
        ContentBoundary after r ds z' result input origin base' ys ∧
        StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
        d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
        fillEnd result = fillEnd d ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧ next.brk = st.brk ∧
        (next.ret = st.ret ∨ next.ret = some need_more) ∧
        ((base' = base ∧ ys = xs ∧ next.bflush = false) ∨ (ys = [] ∧ next.bflush = true)) ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) := by
    let next : LoopS := if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
      else { st with hash_head := head, bflush := true }
    refine ⟨produced, next, after, z', result, nextBase, [], compose decision, state, buffersA, accountA, clearA,
      progress, less, endpoint, ?_, baseLe, ?_, ?_, Or.inr ⟨rfl, ?_⟩, configA, lowA, phaseA, ?_, ?_⟩
    · obtain ⟨_, _, trees, ledger, _⟩ := state.symbols
      have count := ledger.count
      have extent := trees.base.sym_end
      have lower := trees.base.lit_lo
      simp only [List.length_nil, Nat.mul_zero] at count
      omega
    · dsimp only [next]; split <;> rfl
    · dsimp only [next]; split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · dsimp only [next]; split <;> rfl
    · intro _ continued
      by_cases empty : z'.avail_out = 0
      · simp [next, empty] at continued
      · have nonzero : z'.avail_out.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
    · intro returned
      by_cases empty : z'.avail_out = 0
      · exact Or.inr empty
      · have same : next.ret = st.ret := by simp [next, empty]
        exact Or.inl (same.symm.trans returned)
  by_cases selected : (df.prev_length ≥ MIN_MATCH_u && df.match_length ≤ df.prev_length) = true
  · have previous : 3 ≤ df.prev_length.toNat := by
      have guard := selected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      exact UInt32.le_iff_toNat_le.mp guard.1
    have available : df.match_available ≠ 0 := (previousHistory.2 previous).2.1
    have accountF : base + represented xs + 1 = origin + df.strstart.toNat := by
      change base + represented xs + 1 = origin + d.strstart.toNat
      change d.match_available ≠ 0 at available
      simpa only [pendingCredit, available, ite_false] using boundary.accounted
    obtain ⟨produced, head, after, z', result, decision, state, buffersA, accountA, clearA, startA, lookA, endpoint, configA, lowA, phaseA⟩ :=
      slow_match_full_flush_loop goodF symbolF buffersF chainsF env.win getF previousHistory selected lookahead boundary.range formF
        full insert positive pointer cursor memory pending bits clearF boundary.trace accountF view flush st candidate
    change result.strstart.toNat = d.strstart.toNat + (df.prev_length.toNat - 1) at startA
    change result.lookahead.toNat = d.lookahead.toNat - (df.prev_length.toNat - 1) at lookA
    exact fullNext decision state buffersA accountA clearA (by omega) (by omega) endpoint (Nat.le_add_right _ _)
        ((ConfigFrame.slow searchFrame).trans configA) lowA phaseA
  · have branch := Bool.eq_false_iff.mpr selected
    have matching : 3 ≤ df.match_length.toNat →
        GoodMatch wa df.strstart.toNat df.w_size.toNat df.match_start.toNat df.match_length.toNat := by
      intro large
      exact quality large (literal_search_improves branch large)
    have counts := advance_one_counts goodF.inv boundary.range (by change 1 ≤ d.lookahead.toNat; omega)
    by_cases available : df.match_available = 0
    · let result := deferOne df
      let after := setD found ds result
      have kept := defer_one_good goodF chainsF boundary.range (by change 1 ≤ d.lookahead.toNat; omega)
      have symbolic := slow_defer_symbol_boundary goodF symbolF chainsF boundary.range
        (by change 1 ≤ d.lookahead.toNat; omega) branch available flush st candidate
      have current := window_lazy_history_defer goodF.inv boundary.range lookahead lengthF matching
      have endpoint : fillEnd result = fillEnd d := counts.2.2
      have historyA : LazyHistory input origin result := window_history_logical current (by
        intro i fit
        change i < fillEnd result at fit
        rw [endpoint] at fit
        exact view i fit)
      have startA : result.strstart.toNat = d.strstart.toNat + 1 := counts.1
      have lookA : result.lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
      have chainsA : HeapChains after result result.strstart.toNat := by rw [startA]; exact kept.2.1
      have insertA : result.insert = 0 := insert
      have goodA : DGood after r ds z result := kept.1
      have ownedA := stream_owned_keys goodF goodA rfl rfl rfl rfl
      have buffersA := stream_buffers_private_read goodF.live.hz goodA.live.hz buffersF (byte_frame_setD found ds result)
        (fun b equal => (stream_owned_deflate goodF b).mpr (Or.inl equal)) ownedA (stream_accounting_zero z)
      have clearA := clearF.slow symbolic.2.2
      have frameA := searchFrame.trans symbolic.2.2
      have configA := ConfigFrame.slow frameA
      have initialReady : PublishReady d := ⟨pending, cursor, by omega⟩
      have readyA := initialReady.slow frameA
      have state : ContentBoundary after r ds z result input origin base xs := by
        refine ⟨⟨⟨goodA, chainsA, kept.2.2, historyA, ?_, symbolic.2.1, ?_⟩, ?_, ?_, fun _ => insertA⟩,
          boundary.trace, ?_⟩
        · intro _
          rw [startA]
          omega
        · refine ⟨w, wa, env.win, getF, ?_, ?_⟩
          · intro i fit
            rw [endpoint] at fit
            exact view i fit
          · intro _
            change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat key
            rw [startA]
            exact formF
        · simp only [insertA, show (0 : UInt32).toNat = 0 from rfl]
          exact Nat.zero_le _
        · simpa only [insertA, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
        · have account0 : base + represented xs = origin + d.strstart.toNat := by
            change d.match_available = 0 at available
            simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
          change base + represented xs + pendingCredit (deferOne df) = origin + result.strstart.toNat
          rw [show pendingCredit (deferOne df) = 1 from rfl, startA]
          omega
      refine ⟨0, { st with hash_head := candidate, bflush := false }, after, z, result, base, xs,
        compose symbolic.1, state, buffersA, stream_accounting_zero z, clearA, ?_, ?_, endpoint,
        ?_, Nat.le_refl _, rfl, Or.inl rfl, Or.inl ⟨rfl, rfl, rfl⟩, configA, readyA.2.2, fun _ => readyA, fun space _ => space, fun returned => Or.inl returned⟩
      · omega
      · omega
      · change d.sym_next.toNat < d.sym_end.toNat
        omega
    · have current := window_lazy_history_advance goodF.inv boundary.range lookahead lengthF available matching
      have historyF : LazyHistory input origin (advanceOne df) := window_history_logical current (by
        intro i fit
        rw [counts.2.2] at fit
        exact view i fit)
      have accountF : base + represented xs + 1 = origin + df.strstart.toNat := by
        change base + represented xs + 1 = origin + d.strstart.toNat
        change d.match_available ≠ 0 at available
        simpa only [pendingCredit, available, ite_false] using boundary.accounted
      have balanceF : BlockBalance df xs 1 := by
        change BlockBalance d xs 1
        change d.match_available ≠ 0 at available
        simpa only [deferredCredit, available, ite_false] using balance
      obtain ⟨produced, after, z', result, decision, state, buffersA, accountA, clearA, startA, lookA, endpoint, configA, lowA, phaseA⟩ :=
        slow_literal_full_flush_loop_content goodF treesF buffersF chainsF positive pointer cursor memory pending bits
          ledgerF clearF boundary.trace env.win getF boundary.range (by change 1 ≤ d.lookahead.toNat; omega)
          (boundary.deferred available) balanceF accountF view branch available full flush st candidate insert historyF formF
      change result.strstart.toNat = d.strstart.toNat + 1 at startA
      change result.lookahead.toNat = d.lookahead.toNat - 1 at lookA
      exact fullNext decision state buffersA accountA clearA (by omega) (by omega) endpoint (Nat.le_add_right _ _)
        ((ConfigFrame.slow searchFrame).trans configA) lowA phaseA

/-- Every actual ready-lookahead iteration preserves the initialized
content boundary, including all full-buffer encodings and both kinds
of symbol emission. Aligned strict symbol count derives tally room;
no extra room or selected-branch premise is assumed. This is one body
iteration; refill, EOF/flush tails and the outer loop remain separate. -/
theorem slow_body_ready_all_loop {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (lookahead : 262 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
      (base' : Nat) (ys : List Symbol),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧
      next.brk = st.brk ∧ (next.ret = st.ret ∨ next.ret = some need_more) ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (0 < z.avail_out.toNat → next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) := by
  have room := literal_room boundary.good.inv strict
  by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
  · obtain ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA,
      progress, less, endpoint, countA, baseLe, brkA, retA, _casesA, configA, lowA, phaseA, continuedA, reasonA⟩ :=
      slow_body_full_slot_loop boundary buffers positive pointer cursor memory pending bits clear lookahead full flush st
    exact ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA,
      progress, less, endpoint, countA, baseLe, brkA, retA, configA, lowA, phaseA, continuedA, reasonA⟩
  · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
    obtain ⟨next, after, result, ys, run, state, frameA, progress, less, endpoint, _step, countA,
      brkA, retA, buffersA, _storageA, reasonA⟩ := slow_body_content_buffers_reason boundary lookahead space buffers flush st
    have readyA := PublishReady.slow (show PublishReady d from ⟨pending, cursor, by omega⟩) frameA
    exact ⟨0, next, after, z, result, base, ys, run, state, buffersA, stream_accounting_zero z,
      clear.slow frameA, progress, less, endpoint, countA, Nat.le_refl _, brkA, retA, ConfigFrame.slow frameA,
      readyA.2.2, fun _ => readyA, fun space _ => space, reasonA⟩

/-- An actual ready iteration preserves the stronger strategy boundary
that default initialization establishes. Positive remaining output permits
another iteration with the same fixed configuration and publication phase.
The complete emitted-block history and short-lookahead paths are separate. -/
theorem slow_body_strategy_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (positive : 0 < config.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (output : 0 < z.avail_out.toNat) (lookahead : 262 ≤ d.lookahead.toNat) (flush : Int32) (st : LoopS) :
    ∃ (produced : Nat) (next : LoopS) (after : Heap) (z' : ZStream) (result : DeflateState)
      (base' : Nat) (ys : List Symbol),
      deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result input origin base' ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ base ≤ base' ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧ (next.ret = none → 0 < z'.avail_out.toNat) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) := by
  have ready := boundary.resume output
  have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
  have memoryEq : d.lit_bufsize = config.memory := congrArg EngineConfig.memory boundary.configuration
  obtain ⟨produced, next, after, z', result, base', ys, run, state, buffersA, accountA, clearA,
    progress, less, endpoint, countA, baseLe, brkA, retA, frame, lowA, phaseA, continuedA, reasonA⟩ :=
    slow_body_ready_all_loop boundary.toContentBoundary buffers (by rw [levelEq]; exact positive)
      pointer ready.2.1 (by rw [memoryEq]; exact memory) ready.1 (by have := ready.2.2; omega)
      boundary.clear lookahead boundary.strict flush st
  exact ⟨produced, next, after, z', result, base', ys, run,
    ⟨state, Eq.trans frame boundary.configuration, clearA, lowA, countA, phaseA⟩,
    buffersA, accountA, progress, less, endpoint, baseLe, brkA, retA, continuedA output, reasonA⟩

end Zlib.Deflate.Engine.Proofs
