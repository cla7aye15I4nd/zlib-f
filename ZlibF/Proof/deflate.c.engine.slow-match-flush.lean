import ZlibF.Proof.«deflate.c.engine.flush-control»

/-! # The actual full match decision consumes the match before flushing -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real selected-match decision fills the symbol buffer, executes
the complete match-consumption/insertion loop, then flushes and obeys the
actual need_more return. Logical previous-match bytes supply the emitted
symbol's meaning. This is an internal selected decision cutpoint. -/
theorem slow_match_full_flush {h : Heap} {r : ZStreamRef} {ds ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (buffers : StreamBuffers h r)
    (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (lookahead : 262 ≤ d.lookahead.toNat) (range : fillEnd d ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (full : d.sym_next.toNat + 3 = d.sym_end.toNat) (insert : d.insert = 0)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (trace : Trace input base xs) (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ (produced : Nat) (head : UInt32) (after : Heap) (z' : ZStream) (result : DeflateState),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedMatch d])) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have bounds := logical_previous_tally_bounds history previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  have distancePositive : 1 ≤ distance.toNat := bounds.1
  have lengthBound : length.toNat ≤ 255 := bounds.2.2.2.1
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have available : d.match_available ≠ 0 := (history.2 previous).2.1
  have credit : deferredCredit d = 1 := by simp [deferredCredit, available]
  rw [credit] at balance
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := Nat.le_of_eq full
  let bytes := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b bytes) ds dt
  have goodT : DGood ht r ds z dt := match_good_after good trees distance length room
  have chainsT : HeapChains ht dt (d.strstart.toNat + 1) := by
    obtain ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩ :=
      pending_write_chains good chains trees.base.pbuf bytes 0
    exact ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩
  have getT : ht.bytes w = some wa := pending_window_frame good win trees.base.pbuf get bytes dt
  have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have flag : (d.sym_next + 3 == d.sym_end) = true := by
    apply beq_iff_eq.mpr
    apply UInt32.toNat_inj.mp
    rw [count]
    exact full
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (true, ht) := by
    simpa only [flag, ht, dt, bytes, matchSymbolState] using tally_match_run trees.base distance length bounds.1 bounds.2.1 room
  obtain ⟨candidate, after, result, advance, goodA, chainsA, winA, bytesA, availableA, lengthA,
      previousA, startA, lookA, endpoint, rangeA, formA, keep, _, bytesFrame, blockFrame, literalFrame, distanceFrame, recordFrame, storageAdvance⟩ :=
    slow_match_advance_storage goodT chainsT win getT previous history.1 lookahead range form hash_head
  have ledgerT : SymbolLedger bytes dt (xs ++ [emittedMatch d]) :=
    ledger_match trees.base ledger room distance length distancePositive bounds.2.1 (by omega)
  have ledgerA : SymbolLedger bytes result (xs ++ [emittedMatch d]) :=
    ledgerT.keep keep.2.2.2.2.2.2.2.2.2.2 keep.2.2.2.1 literalFrame distanceFrame
  have pendingA : result.pending_buf = .ref (.blk b) 0 := keep.1.trans trees.base.pbuf
  have dataA : after.bytes b = some bytes := by rw [bytesFrame]; simp [ht]
  have emittedSize : (emittedMatch d).bytes = d.prev_length.toNat := by
    change (if distance.toNat = 0 then 1 else length.toNat + 3) = _
    rw [if_neg (by omega)]
    have len : length.toNat = d.prev_length.toNat - 3 := bounds.2.2.1
    omega
  have balanceA : BlockBalance result (xs ++ [emittedMatch d]) (deferredCredit result) := by
    have availableZero : deferredCredit result = 0 := by simp [deferredCredit, availableA]
    rw [availableZero]
    unfold BlockBalance at balance ⊢
    rw [represented_snoc, emittedSize]
    change result.block_start = d.block_start at blockFrame
    change result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) at startA
    rw [blockFrame, startA]
    omega
  have symbolA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  have recordA : SlowRecordFrame d result := by
    unfold SlowRecordFrame
    rw [recordFrame]
    rfl
  have tallyFrame := pending_state_byte_frame h ds b d dt bytes trees.base.pbuf
  have tallyOwned := stream_owned_keys good goodT rfl rfl rfl rfl
  have buffersT := stream_buffers_private_read good.live.hz goodT.live.hz buffers tallyFrame
    (fun b owned => (stream_owned_deflate good b).mpr owned) tallyOwned (stream_accounting_zero z)
  have advanceOwned := stream_owned_keys goodT goodA
    (by rw [recordA]; rfl) (by rw [recordA]; rfl) (by rw [recordA]; rfl) (by rw [recordA]; rfl)
  have buffersA := stream_buffers_private_read goodT.live.hz goodA.live.hz buffersT storageAdvance
    (fun b equal => (stream_owned_deflate goodT b).mpr (Or.inl equal)) advanceOwned (stream_accounting_zero z)
  have insertA : result.insert = 0 := by rw [recordA]; exact insert
  have currentHistory : LazyHistory input origin result := logical_history_initial lengthA input origin
  have clearA := clear.slow recordA
  let retained : DeflateState := { d with match_start := d.prev_match, match_length := d.prev_length }
  have previousHistory : LazyHistory input origin retained := history
  have meaning := retained_match_input_meaning previousHistory window previous
  change (emittedMatch d).Meaning input (origin + d.strstart.toNat - 1) at meaning
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceA := trace.snoc meaning
  change result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) at startA
  have accountedA : base + represented (xs ++ [emittedMatch d]) + pendingCredit result = origin + result.strstart.toNat := by
    simp only [pendingCredit, availableA, ite_true, Nat.add_zero]
    rw [represented_snoc, emittedSize, startA]
    omega
  have boundaryA : ContentBoundary after r ds z result input origin base (xs ++ [emittedMatch d]) := by
    refine ⟨⟨⟨goodA, chainsA, rangeA, currentHistory, ?_, symbolA, ?_⟩, ?_, ?_, fun _ => insertA⟩,
      traceA, accountedA⟩
    · intro available
      exact False.elim (available availableA)
    · refine ⟨w, wa, winA, bytesA, ?_, fun _ => formA⟩
      intro i bound
      change i < result.strstart.toNat + result.lookahead.toNat at bound
      rw [endpoint] at bound
      exact view i bound
    · simp only [insertA, show (0 : UInt32).toNat = 0 from rfl]
      exact Nat.zero_le _
    · simpa only [insertA, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
  obtain ⟨produced, flushedHeap, z', flushed, flushRun, boundaryF, buffersF, accountF, clearF, frameF⟩ :=
    flush_nonfinal_content_boundary boundaryA buffersA
      (by rw [recordA]; exact positive) pointer (by rw [recordA]; exact cursor)
      (by rw [recordA]; exact memory) (by rw [recordA]; exact pending)
      (by rw [recordA]; exact bits) clearA availableA
  have flushStart : flushed.strstart = result.strstart := by rw [frameF]
  have flushLook : flushed.lookahead = result.lookahead := by rw [frameF]
  refine ⟨produced, candidate, flushedHeap, z', flushed, ?_, boundaryF, buffersF, accountF, clearF,
    ?_, ?_, ?_⟩
  · have advance' : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u)
        hash_head ht = .ok (candidate, after) := advance
    dsimp only [distance, length] at tally
    unfold slowDecision
    simp only [bind_app, ldDeflateState_tab good.live.hs, selected, ite_true, tally]
    simp only [bind_app, advance', flushRun]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
  · rw [flushStart]; exact startA
  · rw [flushLook]; exact lookA
  · change flushed.strstart.toNat + flushed.lookahead.toNat = _
    rw [flushStart, flushLook]
    exact endpoint

end Zlib.Deflate.Engine.Proofs
