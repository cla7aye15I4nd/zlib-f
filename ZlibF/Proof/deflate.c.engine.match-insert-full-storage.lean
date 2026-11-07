import ZlibF.Proof.«deflate.c.engine.search-full-storage»
import ZlibF.Proof.«deflate.c.engine.short-match-frontier»

/-! # Complete heap effects of actual selected-match consumption -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual insertion retains the full frame at the saved valid-data endpoint. -/
theorem current_insert_full_storage_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (ordered : top ≤ d.strstart.toNat)
    (range : validEnd ≤ d.window_size.toNat)
    (data : d.strstart.toNat + 3 ≤ validEnd)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key candidate after,
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      DGood after r ds z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (d.strstart.toNat + 1) validEnd ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, candidate, after, run, goodA, chainsA, bytesA, formA, storageA⟩ :=
    current_insert_storage_at good chains win get ordered range data form
  obtain ⟨wb, p, q, a, pa, qa, env, _hash⟩ := heap_chains_at_environment good chains
  have extent := window_extent good env.win env.wbytes
  obtain ⟨shape, full, _live, alloc, next⟩ :=
    insert_string_run_full_storage good env d.strstart (by omega) (by omega) run
  exact ⟨key, candidate, after, run, goodA, chainsA, bytesA, formA, storageA, shape, full, alloc, next⟩

/-- One actual guarded match-consumption step retains the full private footprint, including the EOF skip branch. -/
theorem slow_match_insert_step_frontier_full_storage {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d)
    (chains : HeapChainsAt h d (min (d.strstart.toNat + 1) (validEnd - 2)) validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.prev_length.toNat)
    (room : d.strstart.toNat + d.prev_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (valid : validEnd ≤ d.window_size.toNat)
    (max_insert : UInt32) (maximum : max_insert.toNat + 3 = validEnd)
    (form : d.strstart.toNat + 1 ≤ max_insert.toNat →
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ key candidate mid after,
      let result := countDown { bumpStart d with ins_h := key }
      slowMatchBody (some (.tab ds)) max_insert hash_head h = .ok (candidate, mid) ∧
      slowMatchCond (some (.tab ds)) candidate mid = .ok ((result.prev_length != 0, candidate), after) ∧
      DGood after r ds z result ∧ HeapChainsAt after result (min (result.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.prev_length.toNat = d.prev_length.toNat - 1 ∧
      (result.strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have bumped := bump_start_good_at good chains win get (by omega)
  let hb := setD h ds (bumpStart d)
  have getB : hb.bytes w = some wa := get
  have write : wr (some (.tab ds)) bumpStart h = .ok ((), hb) := by
    simp [wrD_eq, good.live.hs, hb]
  have source : slowMatchBody (some (.tab ds)) max_insert hash_head h =
      (do
        let ss ← rd (some (.tab ds)) (·.strstart)
        if ss ≤ max_insert then INSERT_STRING (some (.tab ds)) ss else pure hash_head) hb := by
    unfold slowMatchBody
    change (do
      wr (some (.tab ds)) bumpStart
      let ss ← rd (some (.tab ds)) (·.strstart)
      if ss ≤ max_insert then INSERT_STRING (some (.tab ds)) ss else pure hash_head) h = _
    rw [bind_app, write]
  have stateB : hb.dstates ds = some (bumpStart d) := bumped.2.1.live.hs
  have body : ∃ key candidate mid,
      slowMatchBody (some (.tab ds)) max_insert hash_head h = .ok (candidate, mid) ∧
      DGood mid r ds z { bumpStart d with ins_h := key } ∧
      HeapChainsAt mid { bumpStart d with ins_h := key }
        (min ((bumpStart d).strstart.toNat + 1) (validEnd - 2)) validEnd ∧ mid.bytes = h.bytes ∧
      ((bumpStart d).strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm d.hash_shift d.hash_mask (bfn wa) ((bumpStart d).strstart.toNat + 1) key) ∧
      ByteFrame h mid (fun i => i = ds) ∧
      Shape h mid ∧ Frame h mid (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ mid.nalloc = h.nalloc ∧ mid.nextBlk = h.nextBlk := by
    by_cases guard : (bumpStart d).strstart ≤ max_insert
    · have ordered : min (d.strstart.toNat + 1) (validEnd - 2) ≤ (bumpStart d).strstart.toNat := by
        rw [bumped.1]; exact Nat.min_le_left _ _
      have data : (bumpStart d).strstart.toNat + 3 ≤ validEnd := by
        have bound := UInt32.le_iff_toNat_le.mp guard
        omega
      have primed : InsHForm (bumpStart d).hash_shift (bumpStart d).hash_mask (bfn wa)
          (bumpStart d).strstart.toNat (bumpStart d).ins_h := by
        change InsHForm d.hash_shift d.hash_mask (bfn wa) (bumpStart d).strstart.toNat d.ins_h
        rw [bumped.1]
        exact form (by have bound := UInt32.le_iff_toNat_le.mp guard; rw [bumped.1] at bound; exact bound)
      obtain ⟨key, candidate, mid, run, goodI, chainsI, bytesI, formI, storageI, shapeI, fullI, allocI, nextI⟩ :=
        current_insert_full_storage_at bumped.2.1 bumped.2.2 win getB ordered valid data primed
      have frontierEq : min ((bumpStart d).strstart.toNat + 1) (validEnd - 2) =
          (bumpStart d).strstart.toNat + 1 := Nat.min_eq_left (by omega)
      have frontierI : HeapChainsAt mid { bumpStart d with ins_h := key }
          (min ((bumpStart d).strstart.toNat + 1) (validEnd - 2)) validEnd := by
        rw [frontierEq]; exact chainsI
      have shapeB := shape_setD good.live.hs (bumpStart d)
      have fullB : Frame h hb (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
        full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
      have full := full_frame_trans_shape fullB fullI shapeB
      refine ⟨key, candidate, mid, ?_, goodI, frontierI, bytesI, fun _ => formI,
        (byte_frame_setD h ds (bumpStart d)).trans storageI, shapeB.trans shapeI, full, allocI, nextI⟩
      rw [source]
      simp only [bind_app, rdD_eq, stateB, guard, ite_true]
      exact run
    · have keep : { bumpStart d with ins_h := d.ins_h } = bumpStart d := rfl
      have later : ¬ (bumpStart d).strstart.toNat + 1 ≤ max_insert.toNat := by
        have bound : ¬ (bumpStart d).strstart.toNat ≤ max_insert.toNat := by
          intro le; exact guard (UInt32.le_iff_toNat_le.mpr le)
        omega
      refine ⟨d.ins_h, hash_head, hb, ?_, bumped.2.1,
        bumped.2.2.raise (by have ss := bumped.1; omega), rfl, ?_, byte_frame_setD h ds (bumpStart d), shape_setD good.live.hs _,
        full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same)), rfl, rfl⟩
      · rw [source]
        simp only [bind_app, rdD_eq, stateB, guard, ite_false]
        rfl
      · intro le; exact False.elim (later le)
  obtain ⟨key, candidate, mid, bodyRun, goodI, chainsI, bytesI, formI, storageI, shapeI, fullI, allocI, nextI⟩ := body
  let di := { bumpStart d with ins_h := key }
  let after := setD mid ds (countDown di)
  have kept := count_down_good_at goodI chainsI
  have ss : (countDown di).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have count : (countDown di).prev_length.toNat = d.prev_length.toNat - 1 := u32_sub_one positive
  have condition : slowMatchCond (some (.tab ds)) candidate mid =
      .ok (((countDown di).prev_length != 0, candidate), after) := by
    unfold slowMatchCond
    change (do
      wr (some (.tab ds)) countDown
      pure ((← rd (some (.tab ds)) (·.prev_length)) != 0, candidate)) mid = _
    have put : wr (some (.tab ds)) countDown mid = .ok ((), after) := by
      simp [wrD_eq, goodI.live.hs, after, di]
    rw [bind_app, put]
    have stateA : after.dstates ds = some (countDown di) := kept.1.live.hs
    simp only [bind_app, rdD_eq, stateA]
    rfl
  have shapeD := shape_setD goodI.live.hs (countDown di)
  have fullD : Frame mid after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame mid ds _) (fun _ same => Or.inr (Or.inl same))
  have full := full_frame_trans_shape fullI fullD shapeI
  exact ⟨key, candidate, mid, after, bodyRun, condition, kept.1, kept.2,
    by change mid.bytes w = some wa; rw [bytesI]; exact get,
    ss, count, formI, bytesI,
    storageI.trans (byte_frame_setD mid ds (countDown di)), shapeI.trans shapeD, full, allocI, nextI⟩

set_option maxHeartbeats 2000000 in
/-- The actual guarded consumption loop terminates with its exact object and allocation ledger. -/
theorem slow_match_insert_loop_frontier_full_storage {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChainsAt h d (min (d.strstart.toNat + 1) (validEnd - 2)) validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.prev_length.toNat) (countBound : d.prev_length.toNat ≤ 256)
    (room : d.strstart.toNat + d.prev_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (valid : validEnd ≤ d.window_size.toNat)
    (max_insert : UInt32) (maximum : max_insert.toNat + 3 = validEnd)
    (form : d.strstart.toNat + 1 ≤ max_insert.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      cdoWhile (slowMatchBody (some (.tab ds)) max_insert) (slowMatchCond (some (.tab ds))) hash_head h =
        .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChainsAt after result (min (result.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.prev_length.toNat ∧ result.lookahead = d.lookahead ∧
      result.strstart.toNat + 1 + result.lookahead.toNat ≤ result.window_size.toNat ∧
      (result.strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      MatchInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧ Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let total := d.strstart.toNat + d.prev_length.toNat
  let Inv : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChainsAt heap state (min (state.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    1 ≤ state.prev_length.toNat ∧ state.prev_length.toNat ≤ 256 ∧
    state.lookahead = d.lookahead ∧
    state.strstart.toNat + state.prev_length.toNat = total ∧
    state.strstart.toNat + state.prev_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    validEnd ≤ state.window_size.toNat ∧
    (state.strstart.toNat + 1 ≤ max_insert.toNat →
      InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h) ∧
    MatchInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let Q : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChainsAt heap state (min (state.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧ state.prev_length = 0 ∧
    state.strstart.toNat = total ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    (state.strstart.toNat + 1 ≤ max_insert.toNat →
      InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h) ∧
    MatchInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let rank : UInt32 → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.prev_length.toNat)).getD 0
  have step : ∀ hh heap, Inv hh heap → ∃ hh1 h1 c hh2 h2,
      slowMatchBody (some (.tab ds)) max_insert hh heap = .ok (hh1, h1) ∧
      slowMatchCond (some (.tab ds)) hh1 h1 = .ok ((c, hh2), h2) ∧
      (c = false → Q hh2 h2) ∧ (c = true → Inv hh2 h2 ∧ rank hh2 h2 < rank hh heap) := by
    intro hh heap inv
    obtain ⟨state, goodS, chainsS, winS, bytesS, posS, boundS, lookEq, sumS, roomS, validS, formS, frameS, byteFrame, storageS, shapeS, fullS, allocS, nextS⟩ := inv
    obtain ⟨key, candidate, mid, after, bodyRun, condRun, goodA, chainsA, bytesA, startA, countA, formA, bytesEq, storageA, shapeA, fullA, allocA, nextA⟩ :=
      slow_match_insert_step_frontier_full_storage goodS chainsS winS bytesS posS roomS validS max_insert maximum formS hh
    let result := countDown { bumpStart state with ins_h := key }
    have sumA : result.strstart.toNat + result.prev_length.toNat = total := by rw [startA, countA]; omega
    have roomA : result.strstart.toNat + result.prev_length.toNat + 1 + result.lookahead.toNat ≤
        result.window_size.toNat := by
      change result.strstart.toNat + result.prev_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat
      rw [startA, countA]
      omega
    have ownedS : DeflateOwned ds state = DeflateOwned ds d := by
      rw [show state = {d with strstart := state.strstart, ins_h := state.ins_h, prev_length := state.prev_length} from frameS]
      rfl
    have fullA' : Frame heap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      rw [← ownedS]
      exact fullA
    have fullNext := full_frame_trans_shape fullS fullA' shapeS
    refine ⟨candidate, mid, result.prev_length != 0, candidate, after, bodyRun, condRun, ?_, ?_⟩
    · intro stop
      have zero : result.prev_length = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      refine ⟨result, goodA, chainsA, winS, bytesA, zero, ?_, lookEq, ?_, formA, match_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA, shapeS.trans shapeA, fullNext, allocA.trans allocS, nextA.trans nextS⟩
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
    · intro more
      have nonzero : result.prev_length ≠ 0 := by simpa only [bne_iff_ne] using more
      have positiveA : 1 ≤ result.prev_length.toNat := by
        have ne : result.prev_length.toNat ≠ 0 := by intro eq; exact nonzero (UInt32.toNat_inj.mp eq)
        omega
      refine ⟨⟨result, goodA, chainsA, winS, bytesA, positiveA, ?_, lookEq, sumA, roomA, validS, formA, match_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA, shapeS.trans shapeA, fullNext, allocA.trans allocS, nextA.trans nextS⟩, ?_⟩
      · rw [countA]
        omega
      · have stateA : after.dstates ds = some result := goodA.live.hs
        simp only [rank, goodS.live.hs, stateA, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv hash_head h :=
    ⟨d, good, chains, win, get, positive, countBound, rfl, rfl, room, valid, form, rfl, rfl, ByteFrame.refl h _, Shape.refl h, (full_storage_refl h _).2.1, rfl, rfl⟩
  have fuelBound : rank hash_head h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.prev_length.toNat < 18446744073709551616
    omega
  obtain ⟨candidate, after, run, result, post⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨candidate, after, result, run, post⟩


end Zlib.Deflate.Engine.Proofs
