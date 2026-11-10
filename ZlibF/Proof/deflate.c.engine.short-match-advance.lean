import ZlibF.Proof.«deflate.c.engine.short-match-loop»
import ZlibF.Proof.«deflate.c.engine.match-advance»

/-! # Complete selected-match consumption without a long-input premise -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The last source increment rejoins the ordinary window-data endpoint. -/
theorem finish_match_good_at {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d)
    (chains : HeapChainsAt h d (d.strstart.toNat + 1) validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (endpoint : validEnd = d.strstart.toNat + 1 + d.lookahead.toNat) :
    (finishMatch d).strstart.toNat = d.strstart.toNat + 1 ∧
      DGood (setD h ds (finishMatch d)) r ds z (finishMatch d) ∧
      HeapChains (setD h ds (finishMatch d)) (finishMatch d) (finishMatch d).strstart.toNat ∧
      (finishMatch d).strstart.toNat + (finishMatch d).lookahead.toNat ≤ (finishMatch d).window_size.toNat := by
  have bumped := bump_start_good_at good chains win get room
  have inv : DStInv h ds (finishMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have ss : (finishMatch d).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have saved : HeapChainsAt (setD h ds (finishMatch d)) (finishMatch d)
      (d.strstart.toNat + 1) validEnd := chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨ss, good.setD' (d' := finishMatch d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · rw [ss]
    exact saved.collapse (by change validEnd = (finishMatch d).strstart.toNat + d.lookahead.toNat; rw [ss]; exact endpoint)
  · change (finishMatch d).strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
    rw [ss]; exact room

theorem max_insert_nat_bounded {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat) :
    (d.strstart + d.lookahead - MIN_MATCH_u).toNat = d.strstart.toNat + d.lookahead.toNat - 3 := by
  have extent := window_extent good win get
  have sum : (d.strstart + d.lookahead).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  rfl

set_option maxHeartbeats 1500000 in
/-- Actual lookahead consumption, the guarded complete insertion loop and
final lazy reset. Only selected-match bytes are required. The old endpoint
is saved during consumption and the ordinary chain invariant is restored
after the last position increment. The next hash is needed only when at
least three input bytes remain.
-/
theorem slow_match_advance_bounded {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
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
        prev_length := result.prev_length, match_available := 0, match_length := 2 } ∧ ByteFrame h after (fun i => i = ds) := by
  let prepared := prepareMatch d
  let hp := setD h ds prepared
  have counts := prepare_match_counts_bounded d previous length available
  have kept := prepare_match_good_at good chains previous length available
  have getP : hp.bytes w = some wa := get
  have maximum := max_insert_nat_bounded good win get range nonempty
  obtain ⟨candidate, loopHeap, df, loopRun, goodF, chainsF, winF, bytesF, zero, startF, lookF, roomF, formF, frameF, bytesFrame, storageF⟩ :=
    slow_match_insert_loop_at kept.1 kept.2.1 win getP counts.2.2.1 counts.2.2.2.1
      (by rw [counts.2.2.2.2]; exact range) range
      (d.strstart + d.lookahead - MIN_MATCH_u) (by rw [maximum]; omega)
      (by intro le; apply form; rw [maximum] at le; exact le) hash_head
  have finished := finish_match_good_at goodF chainsF winF bytesF roomF (by
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
  have high : result.high_water = d.high_water := by
    change df.high_water = d.high_water
    exact congrArg (·.high_water) frameF
  have keep : TrKeep d result := by
    unfold MatchInsertFrame at frameF
    change TrKeep d (finishMatch df)
    rw [frameF]
    trkeep
  refine ⟨candidate, after, result, ?_, finished.2.1, finished.2.2.1, winF, bytesF,
    rfl, rfl, zero, startA, lookA, endpoint, finished.2.2.2, ?_, keep, high, bytesFrame, ?_, ?_, ?_, ?_,
    ((byte_frame_setD h ds prepared).trans storageF).trans (byte_frame_setD loopHeap ds result)⟩
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


end Zlib.Deflate.Engine.Proofs
