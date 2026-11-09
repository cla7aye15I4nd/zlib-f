import ZlibF.Proof.«deflate.c.engine.flush-macro-counters»
import ZlibF.Proof.«deflate.c.engine.search-controls»

/-! # All actual strategy decisions have exact total counters -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both selected-match paths have exact counters, including full output. -/
theorem slow_match_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.total_in = z.total_in ∧ returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, _emittedStart, _emittedLook, _emittedEnd, _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  have readyE := ready.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨amount, other, otherZ, otherD, flushRun, boundaryA, _endA, _buffersA, accountA, _clearA,
        _frameA, _lowA, _phaseA⟩ :=
      flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1
        (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega) clearE emittedFlag
    have totals := flush_control_run_counter_effects emittedBoundary emittedBuffers
      (by rw [configE.level]; exact positive) pointer readyE.2.1
      (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega)
      clearE emittedFlag false flushRun boundaryA.good.live.hz accountA
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if otherZ.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), other) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, full, ite_true, flushRun]
      by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
    have same := actual_run_stream_unique actualRun run boundaryA.good.live.hz live
    rw [same] at accountA totals
    have count : produced = amount := (stream_accounting_counts_unique account accountA).2
    exact count ▸ totals
  · have nonfull := Bool.eq_false_iff.mpr full
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := head, bflush := false }, emittedHeap) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]
    have same := actual_run_stream_unique actualRun run emittedBoundary.good.live.hz live
    exact unchanged_stream_output_counter_effects_accounted same.symm account

/-- Literal publication precedes its input-position advance; that advance retains totals. -/
theorem slow_literal_full_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.total_in = z.total_in ∧ returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have previousByte := cut.deferred available
  have balance1 : BlockBalance d xs 1 := by simpa only [deferredCredit, available, ite_false] using balance
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  let c := wa[d.strstart.toNat - 1]!
  let dt := literalState d c
  let packed := literalBytes buf d c
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := Nat.le_of_eq full
  have goodT : DGood ht r ds z dt := literal_good_after cut.good trees c room
  have treesT : TreesInvAt ht ds dt pb packed := tally_literal_trees trees c room
  have tallyFrame := pending_state_byte_frame h ds pb d dt packed trees.base.pbuf
  have tallyOwned := stream_owned_keys cut.good goodT rfl rfl rfl rfl
  have buffersT : StreamBuffers ht r := stream_buffers_private_read cut.good.live.hz goodT.live.hz buffers
    tallyFrame (fun b owned => (stream_owned_deflate cut.good b).mpr owned) tallyOwned (stream_accounting_zero z) rfl
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have ledgerT : SymbolLedger packed dt (xs ++ [emittedLiteral d wa]) := ledger_literal trees.base ledger room c
  have balanceT : BlockBalance dt (xs ++ [emittedLiteral d wa]) 0 := by
    simpa only [dt, c, emittedLiteral, show (1 : Int) - 1 = 0 from rfl] using balance_literal balance1 c
  have accountedT : base + represented (xs ++ [emittedLiteral d wa]) = origin + dt.strstart.toNat := by
    rw [represented_snoc, show (emittedLiteral d wa).bytes = 1 from rfl]
    exact accounted
  have meaning := literal_input_meaning cut.deferred available cut.view
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceT := cut.trace.snoc meaning
  have clearT : BlockInit.BlockClear dt := ⟨clear.bl, clear.opt, clear.fixed⟩
  have flag : (d.sym_next + 3 == d.sym_end) = true := by
    apply beq_iff_eq.mpr
    apply UInt32.toNat_inj.mp
    rw [← full]
    exact literal_count trees.base room c
  have tally : tally_lit (some (.tab ds)) c h = .ok (true, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  have bitsT : dt.bi_valid.toInt ≤ 7 := by
    change d.bi_valid.toInt ≤ 7
    have low := ready.2.2
    omega
  obtain ⟨amount, emittedHeap, z', emitted, _written, _remaining, _kind, _body, _padding,
      emitRun, goodE, _buffersE, accountE, _rest⟩ :=
    flush_block_only_publish goodT treesT buffersT positive pointer ready.2.1 memory ready.1
      bitsT ledgerT clearT traceT
      cut.window getT cut.range balanceT accountedT cut.view false
  have totals := flush_macro_run_counter_effects goodT treesT buffersT positive pointer ready.2.1 memory ready.1
    bitsT ledgerT clearT traceT cut.window getT cut.range balanceT accountedT cut.view false emitRun goodE.live.hz accountE
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  let finalD := advanceOne emitted
  let finalHeap := setD emittedHeap ds finalD
  have write : wr (some (.tab ds)) advanceOne emittedHeap = .ok ((), finalHeap) := by
    simp only [wrD_eq, goodE.live.hs, finalHeap, finalD]
  have output : zrd (some r) (·.avail_out) finalHeap = .ok (z'.avail_out, finalHeap) := by
    simp only [zrd_eq, finalHeap, ZStreamRef.get_setD, goodE.live.hz]
  have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
        else { st with hash_head := candidate, bflush := true }), finalHeap) := by
    obtain ⟨size, _⟩ := window_extent cut.good cut.window cut.bytes
    have fit : d.strstart.toNat - 1 < wa.size := by have range := cut.range; dsimp only [fillEnd] at range; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [cut.window, u32_sub_one previousByte]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) cut.bytes (by omega)
    unfold slowDecision
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, branch, Bool.false_eq_true, ite_false,
      hasLiteral, ite_true, read, tally, emitRun0]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head := candidate, bflush := true, ret := some need_more }
      return { st with hash_head := candidate, bflush := true }) emittedHeap = _
    rw [bind_app, write]
    simp only [cut.good.live.back, bind_app, output]
    by_cases fullOut : (z'.avail_out == 0) = true <;> simp [fullOut]
  have getFinal : r.get finalHeap = some z' := by
    simpa only [finalHeap, ZStreamRef.get_setD] using goodE.live.hz
  have same := actual_run_stream_unique actualRun run getFinal live
  rw [same] at accountE totals
  have count : produced = amount := (stream_accounting_counts_unique account accountE).2
  exact count ▸ totals

/-- All actual selected match, literal and defer decisions have exact totals. -/
theorem slow_decision_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.total_in = z.total_in ∧ returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact slow_match_run_counter_effects cut buffers selected strict positive pointer memory ready clear run live account
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st candidate
      have same := actual_run_stream_unique tested run boundaryA.good.live.hz live
      exact unchanged_stream_output_counter_effects_accounted same.symm account
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · exact slow_literal_full_run_counter_effects cut buffers lookahead branch available full positive pointer memory ready clear run live account
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
        have same := actual_run_stream_unique tested run boundaryA.good.live.hz live
        exact unchanged_stream_output_counter_effects_accounted same.symm account

/-- The complete initialized search and decision suffix has exact totals. -/
theorem slow_search_decision_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z returned : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned 0 produced) :
    returned.total_in = z.total_in ∧ returned.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame; rw [searchFrame]
  have configS : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configS
  have positiveS : 1 ≤ searched.lookahead.toNat := by rw [searchFrame]; exact lookahead
  have strictS : searched.sym_next.toNat < searched.sym_end.toNat := by rw [searchFrame]; exact boundary.strict
  have readyS := ready.slow slowFrame
  have clearS := boundary.clear.slow slowFrame
  have decisionRun : slowDecision (some (.tab ds)) flush st head found = .ok (next, after) := by
    unfold slowSearchDecision at run
    simpa only [bind_app, searchRun] using run
  exact slow_decision_run_counter_effects cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory) readyS clearS decisionRun live account

/-- Exact counter witnesses accompany the established actual search suffix. -/
theorem slow_search_decision_counter_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d) (flush : Int32) (st : LoopS) :
    ∃ produced next after z' result,
      slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.total_in = z.total_in ∧
      z'.total_out = z.total_out + UInt64.ofNat produced := by
  obtain ⟨produced, next, after, z', result, _base, _ys, run, stateA, _endA, _buffersA, account, _rest⟩ :=
    slow_search_decision_ready_boundary boundary frontier buffers lookahead room positive pointer memory ready flush st
  have effects := slow_search_decision_run_counter_effects boundary frontier buffers lookahead room positive pointer memory ready
    run stateA.good.live.hz account
  exact ⟨produced, next, after, z', result, run, stateA.good, account, effects⟩

end Zlib.Deflate.Engine.Proofs
