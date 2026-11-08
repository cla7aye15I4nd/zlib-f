import ZlibF.Proof.«deflate.c.engine.short-match-frontier-loop»
import ZlibF.Proof.«deflate.c.engine.short-match-advance»

/-! # Selected-match consumption retains the EOF insertion frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

set_option maxHeartbeats 1500000 in
/-- Actual lookahead consumption, the guarded complete insertion loop and
final lazy reset. Only selected-match bytes are required. The old endpoint
is saved during consumption and the ordinary chain invariant is restored
after the last position increment. The next hash is needed only when at
least three input bytes remain.
-/
theorem slow_match_advance_frontier {h : Heap} {r : ZStreamRef} {ds w : Nat}
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
        prev_length := result.prev_length, match_available := 0, match_length := 2 } ∧ ByteFrame h after (fun i => i = ds) := by
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
  obtain ⟨candidate, loopHeap, df, loopRun, goodF, chainsF, winF, bytesF, zero, startF, lookF, roomF, formF, frameF, bytesFrame, storageF⟩ :=
    slow_match_insert_loop_frontier kept.1 saved win getP counts.2.2.1 counts.2.2.2.1
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
  refine ⟨candidate, after, result, ?_, finished.2.1, finished.2.2.1, frontierA, winF, bytesF,
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
