import ZlibF.Proof.«deflate.c.engine.flush-macro-size»
import ZlibF.Proof.«deflate.c.engine.literal-output-interval»

/-! # Counted output cost of a real full deferred-literal decision -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `local block_state deflate_slow(deflate_state *s, int flush)`
(full deferred-literal decision). The actual tally repays its deferred
byte before the real nonfinal macro. Its byte cost survives the following
advanceOne on the same observed decision run. The full ledger proves one
flushed block represents at least 16,383 bytes. This is an internal
observer, not a completed strategy budget or public API theorem. -/
theorem slow_literal_full_run_byte_count {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z zr : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some zr) (state : after.dstates ds = some result)
    (account : StreamAccounting z zr 0 produced) :
    16383 ≤ represented (xs ++ [emittedLiteral d wa]) ∧
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      (d.bi_valid.toInt.toNat + 7) / 8 + represented (xs ++ [emittedLiteral d wa]) + 5 := by
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
    tallyFrame (fun b owned => (stream_owned_deflate cut.good b).mpr owned) tallyOwned (stream_accounting_zero z) (by rfl)
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
      emitRun, goodE, _buffersE, accountE, _sizesE, storageE, _rest⟩ :=
    flush_block_only_publish goodT treesT buffersT positive pointer ready.2.1 memory ready.1
      bitsT ledgerT clearT traceT
      cut.window getT cut.range balanceT accountedT cut.view false
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  have qualityT : ∀ symbol ∈ xs ++ [emittedLiteral d wa],
      symbol.distance ≠ 0 → symbol.value = 0 → symbol.distance ≤ 4096 := by
    intro symbol member nonzero zero
    rcases List.mem_append.mp member with old | fresh
    · exact quality symbol old nonzero zero
    · have same : symbol = emittedLiteral d wa := List.mem_singleton.mp fresh
      subst symbol
      exact False.elim (nonzero rfl)
  have floorT : StoredSourceFloor dt := floor
  have cost := flush_macro_run_byte_count goodT treesT buffersT positive pointer ready.2.1 memory
    strategy ready.1 bitsT ledgerT clearT traceT qualityT floorT cut.window getT cut.range balanceT
    accountedT cut.view false emitRun goodE.live.hs goodE.live.hz accountE
  have fullT : dt.sym_next = dt.sym_end := by
    apply UInt32.toNat_inj.mp
    change (d.sym_next + 3).toNat = d.sym_end.toNat
    exact (literal_count trees.base room c).trans full
  have blockMinimum := full_ledger_represented_min treesT ledgerT memory fullT

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
  have eq := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
  have finalLive : r.get finalHeap = some z' := by
    simpa only [finalHeap, ZStreamRef.get_setD] using goodE.live.hz
  rw [eq] at finalLive
  have sameZ : z' = zr := Option.some.inj (finalLive.symm.trans live)
  have count : amount = produced := (stream_accounting_counts_unique
    (by simpa only [sameZ] using accountE) account).2
  have finalState : finalHeap.dstates ds = some finalD := setD_dstates_same _ _ _
  rw [eq] at finalState
  have sameD : finalD = result := Option.some.inj (finalState.symm.trans state)
  rw [Zlib.Trees.Proofs.Out.outBits_length] at cost
  have oldBits : dt.pending = 0 := ready.1
  have oldHeld : dt.bi_valid = d.bi_valid := rfl
  rw [oldBits, oldHeld] at cost
  simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at cost
  have pendingSame : result.pending = emitted.pending := by rw [← sameD]; rfl
  have heldSame : result.bi_valid = emitted.bi_valid := by rw [← sameD]; rfl
  rw [count, ← pendingSame, ← heldSame] at cost
  exact ⟨blockMinimum, cost⟩

/-- `local block_state deflate_slow(deflate_state *s, int flush)`
(full deferred-literal decision). Actual execution supplies the returned
content, counters and a single full-block cost on the same heap. The
represented base increment is at least 16,383. No caller contract for
tally, flush or advance is assumed. Output capacity may be zero. -/
theorem slow_literal_full_search_byte_count {h : Heap} {r : ZStreamRef}
    {ds w ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ produced after z' result,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
          else { st with hash_head := candidate, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedLiteral d wa])) [] ∧
      StreamAccounting z z' 0 produced ∧ 16383 ≤ represented (xs ++ [emittedLiteral d wa]) ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + represented (xs ++ [emittedLiteral d wa]) + 5 := by
  obtain ⟨produced, after, z', result, run, boundaryA, _endA, _buffersA, account,
      _clearA, _startA, _lookA, _endpointA, _strictA, _configA, _lowA, _phaseA⟩ :=
    slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer cursor memory pending
      bits clear flush st candidate
  have ready : PublishReady d := ⟨pending, cursor, by omega⟩
  obtain ⟨minimum, cost⟩ := slow_literal_full_run_byte_count cut buffers lookahead branch available full
    positive pointer memory ready clear strategy floor quality run boundaryA.good.live.hz boundaryA.good.live.hs account
  exact ⟨produced, after, z', result, run, boundaryA, account, minimum, cost⟩

end Zlib.Deflate.Engine.Proofs
