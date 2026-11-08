import ZlibF.Proof.«deflate.c.engine.match-insert-full-storage»
import ZlibF.Proof.«deflate.c.engine.short-match-emit-boundary»

/-! # Complete heap effects of actual selected-match consumption -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 2000000 in
/-- Actual match preparation, complete guarded consumption and final lazy reset compose the full private frame. -/
theorem slow_match_advance_frontier_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (min (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (available : d.prev_length.toNat - 1 ≤ d.lookahead.toNat)
    (nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : d.strstart.toNat + 1 ≤ d.strstart.toNat + d.lookahead.toNat - 3 → InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head h =
        .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      HeapChains after result (min result.strstart.toNat (result.strstart.toNat + result.lookahead.toNat - 2)) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.match_available = 0 ∧ result.match_length = 2 ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      (3 ≤ result.lookahead.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h) ∧
      TrKeep d result ∧ result.high_water = d.high_water ∧ after.bytes = h.bytes ∧
      result.block_start = d.block_start ∧ result.dyn_ltree = d.dyn_ltree ∧ result.dyn_dtree = d.dyn_dtree ∧
      result = { d with
        strstart := result.strstart, lookahead := result.lookahead, ins_h := result.ins_h,
        prev_length := result.prev_length, match_available := 0, match_length := 2 } ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let prepared := prepareMatch d
  let hp := setD h ds prepared
  have counts := prepare_match_counts_bounded d previous length available
  have mainChains : HeapChains h d (d.strstart.toNat + 1) :=
    (chains.at.raise (Nat.min_le_left _ _)).collapse rfl
  have kept := prepare_match_good_at good mainChains previous length available
  have saved : HeapChainsAt hp prepared
      (min (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)) (d.strstart.toNat + d.lookahead.toNat) :=
    chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have getP : hp.bytes w = some wa := get
  have maximum := max_insert_nat_bounded good win get range nonempty
  obtain ⟨candidate, loopHeap, df, loopRun, goodF, chainsF, winF, bytesF, zero, startF, lookF, roomF, formF, frameF, bytesFrame, storageF, shapeF, fullF, allocF, nextF⟩ :=
    slow_match_insert_loop_frontier_full_storage kept.1 saved win getP counts.2.2.1 counts.2.2.2.1
      (by rw [counts.2.2.2.2]; exact range) range
      (d.strstart + d.lookahead - MIN_MATCH_u) (by rw [maximum]; omega)
      (by intro le; apply form; rw [maximum] at le; exact le) hash_head
  have finished := finish_match_good_at goodF (chainsF.raise (Nat.min_le_left _ _)) winF bytesF roomF (by
    change d.strstart.toNat + d.lookahead.toNat = df.strstart.toNat + 1 + df.lookahead.toNat
    rw [startF, lookF]
    have same := counts.2.2.2.2
    change d.strstart.toNat + prepared.prev_length.toNat + 1 + prepared.lookahead.toNat = _ at same
    omega)
  let result := finishMatch df
  let after := setD loopHeap ds result
  have writeP : wr (some (.tab ds)) prepareMatch h = .ok ((), hp) := by
    simp [wrD_eq, good.live.hs, hp, prepared]
  have writeF : wr (some (.tab ds)) finishMatch loopHeap = .ok ((), after) := by
    simp [wrD_eq, goodF.live.hs, after, result]
  have startA : result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) := by
    have first : df.strstart.toNat = d.strstart.toNat + prepared.prev_length.toNat := startF
    have final : result.strstart.toNat = df.strstart.toNat + 1 := finished.1
    rw [final, first, counts.2.1]
    omega
  have lookA : result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) := by
    change df.lookahead.toNat = _
    rw [lookF]
    exact counts.1
  have endpoint : result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [startA, lookA]
    omega
  have frontierA : HeapChains after result (min result.strstart.toNat (result.strstart.toNat + result.lookahead.toNat - 2)) := by
    have transferred : HeapChainsAt after result
        (min (df.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)) (d.strstart.toNat + d.lookahead.toNat) :=
      chainsF.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rw [endpoint, finished.1]
    exact transferred.collapse endpoint.symm
  have high : result.high_water = d.high_water := by
    change df.high_water = d.high_water
    exact congrArg (·.high_water) frameF
  have keep : TrKeep d result := by
    unfold MatchInsertFrame at frameF
    change TrKeep d (finishMatch df)
    rw [frameF]
    trkeep
  have shapeP := shape_setD good.live.hs prepared
  have shapeA := shape_setD goodF.live.hs result
  have frameP : Frame h hp (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
  have frameA : Frame loopHeap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame loopHeap ds _) (fun _ same => Or.inr (Or.inl same))
  have shape := (shapeP.trans shapeF).trans shapeA
  have full := full_frame_trans_shape (full_frame_trans_shape frameP fullF shapeP) frameA (shapeP.trans shapeF)
  refine ⟨candidate, after, result, ?_, finished.2.1, finished.2.2.1, frontierA, winF, bytesF,
    rfl, rfl, zero, startA, lookA, endpoint, finished.2.2.2, ?_, keep, high, bytesFrame, ?_, ?_, ?_, ?_,
    ((byte_frame_setD h ds prepared).trans storageF).trans (byte_frame_setD loopHeap ds result), shape, full, full_shape_live_change shape, allocF, nextF⟩
  · unfold slowMatchAdvance
    simp only [initial_match_length]
    change (do
      wr (some (.tab ds)) prepareMatch
      let hh ← cdoWhile (slowMatchBody (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u))
        (slowMatchCond (some (.tab ds))) hash_head
      wr (some (.tab ds)) finishMatch
      pure hh) h = _
    rw [bind_app, writeP]
    simp only []
    rw [bind_app, loopRun]
    simp only []
    rw [bind_app, writeF]
    rfl
  · intro enough
    change InsHForm df.hash_shift df.hash_mask (bfn wa) result.strstart.toNat df.ins_h
    rw [finished.1]
    apply formF
    have la : df.lookahead.toNat = result.lookahead.toNat := rfl
    have endEq : d.strstart.toNat + d.lookahead.toNat = df.strstart.toNat + 1 + df.lookahead.toNat := by
      rw [← endpoint, finished.1]
      rfl
    rw [maximum]
    omega
  · exact congrArg (·.block_start) frameF
  · exact congrArg (·.dyn_ltree) frameF
  · exact congrArg (·.dyn_dtree) frameF
  · unfold MatchInsertFrame at frameF
    dsimp only [result, finishMatch, bumpStart]
    rw [frameF]
    rfl


/-- Selected-match tally and complete guarded match consumption retain
the full private frame, including the short-input skip at EOF. -/
theorem slow_match_emit_run_full_storage {h after : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {input : Nat → UInt8}
    {candidate : UInt32} {flag : Bool}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (hash_head : UInt32)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (run : slowMatchEmit (some (.tab ds)) hash_head h = .ok ((flag, candidate), after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have past := cut.previous.2 previous
  have oldStart := past.1
  have available := past.2.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [cut.good.inv.wsize]
    exact Nat.pow_le_pow_right (by decide) cut.good.inv.wbits_hi
  have bounds := logical_previous_tally_bounds cut.previous previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  have distancePositive : 1 ≤ distance.toNat := bounds.1
  have lengthBound : length.toNat ≤ 255 := bounds.2.2.2.1
  obtain ⟨b, buf, trees, ledger, balance⟩ := cut.symbols
  have credit : deferredCredit d = 1 := by simp only [deferredCredit, available, ite_false]
  rw [credit] at balance
  have room := literal_room cut.good.inv strict
  let packed := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b packed) ds dt
  have goodT : DGood ht r ds z dt := match_good_after cut.good trees distance length room
  have chainsT : HeapChains ht dt (min (d.strstart.toNat + 1) (fillEnd d - 2)) :=
    pending_write_chains cut.good cut.end_frontier trees.base.pbuf packed 0
  have pendingT : HeapChains ht dt (d.strstart.toNat + 1 - d.insert.toNat) :=
    pending_write_chains cut.good cut.frontier trees.base.pbuf packed 0
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have count : dt.sym_next.toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
    tally_match_run trees.base distance length bounds.1 bounds.2.1 room
  have endPositive : 3 ≤ d.strstart.toNat + d.lookahead.toNat := by
    have remaining := bounds.2.2.2.2
    omega
  obtain ⟨head, other, result, advance, _goodA, _chainsA, _endA, _winA, _bytesA, _flagA, _lenA, _prevA,
      _startA, _lookA, _endpoint, _rangeA, _formA, _keep, _high, _bytesFrame, _blockFrame, _literalFrame,
      _distanceFrame, _recordA, _storageA, shapeA, fullA, _liveA, allocA, nextA⟩ :=
    slow_match_advance_frontier_full_storage goodT chainsT cut.window getT previous cut.previous.1 bounds.2.2.2.2
      endPositive cut.range (by intro enough; apply cut.primed; change d.strstart.toNat + 1 ≤ d.strstart.toNat + d.lookahead.toNat - 3 at enough; omega) hash_head
  change slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head ht = .ok (head, other) at advance
  have tested : slowMatchEmit (some (.tab ds)) hash_head h = .ok ((d.sym_next + 3 == d.sym_end, head), other) := by
    dsimp only [distance, length] at tally
    unfold slowMatchEmit
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, tally, advance, pure_app]
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  have tallyStorage : OutputStorage h ht r ds b b := output_bits_storage cut.good.live.hs trees.base.bytes
  have tallyFrame : Frame h ht (fun k => StreamRoot r k ∨ DeflateOwned ds d k) := by
    apply full_frame_weaken tallyStorage.frame
    intro k owned
    rcases owned with root | same | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst k; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    · subst k; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have shape := tallyStorage.shape.trans shapeA
  have full := full_frame_trans_shape tallyFrame fullA tallyStorage.shape
  exact ⟨shape, full, full_shape_live_change shape, allocA, nextA⟩

end Zlib.Deflate.Engine.Proofs
