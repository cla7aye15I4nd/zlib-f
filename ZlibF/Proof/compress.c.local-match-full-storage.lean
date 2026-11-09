import ZlibF.Proof.«compress.c.local-match-symbols»
import ZlibF.Proof.«deflate.c.engine.search-full-storage»

/-! # Complete typed effects of actual local selected-match consumption

The actual state stores and guarded head/prev insertion writes compose a
full typed frame through the ranked loop and final lazy reset. The original
owner roots remain fixed. No byte-only frame is used as a typed frame.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchFullStorage
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Spec.Public.Proofs.CompressLocalSearch
open ZlibF.Spec.Public.Proofs.CompressLocalMatchEndpoint
open ZlibF.Spec.Public.Proofs.CompressLocalMatchTally
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
variable {cutoff : Nat}

/-- Actual insertion retains the full frame at the saved valid-data endpoint. -/
theorem local_current_insert_full_storage_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (ordered : top ≤ d.strstart.toNat)
    (range : validEnd ≤ d.window_size.toNat)
    (data : d.strstart.toNat + 3 ≤ validEnd)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key candidate after,
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      LocalState after cutoff r ds z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (d.strstart.toNat + 1) validEnd ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, candidate, after, run, goodA, chainsA, bytesA, formA, storageA⟩ :=
    local_current_insert_storage_at good chains win get ordered range data form
  obtain ⟨wb, p, q, a, pa, qa, env, _hash⟩ := local_heap_chains_at_environment good chains
  have extent := local_window_extent good env.win env.wbytes
  obtain ⟨shape, full, _live, alloc, next⟩ :=
    local_insert_string_storage good env d.strstart (by omega) (by omega) run
  exact ⟨key, candidate, after, run, goodA, chainsA, bytesA, formA, storageA, shape, full, alloc, next⟩

/-- One actual guarded match-consumption step retains the full private footprint, including the EOF skip branch. -/
theorem local_match_insert_step_full_storage {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d)
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
      LocalState after cutoff r ds z result ∧ HeapChainsAt after result (min (result.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.prev_length.toNat = d.prev_length.toNat - 1 ∧
      (result.strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have bumped := local_bump_start_good_at good chains win get (by omega)
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
      LocalState mid cutoff r ds z { bumpStart d with ins_h := key } ∧
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
        local_current_insert_full_storage_at bumped.2.1 bumped.2.2 win getB ordered valid data primed
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
  have kept := local_count_down_good_at goodI chainsI
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
theorem local_match_insert_loop_full_storage {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d (min (d.strstart.toNat + 1) (validEnd - 2)) validEnd)
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
      LocalState after cutoff r ds z result ∧ HeapChainsAt after result (min (result.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.prev_length.toNat ∧ result.lookahead = d.lookahead ∧
      result.strstart.toNat + 1 + result.lookahead.toNat ≤ result.window_size.toNat ∧
      (result.strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      MatchInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧ Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let total := d.strstart.toNat + d.prev_length.toNat
  let Inv : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    LocalState heap cutoff r ds z state ∧ HeapChainsAt heap state (min (state.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
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
    LocalState heap cutoff r ds z state ∧ HeapChainsAt heap state (min (state.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
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
      local_match_insert_step_full_storage goodS chainsS winS bytesS posS roomS validS max_insert maximum formS hh
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


set_option maxHeartbeats 2000000 in
/-- Actual match preparation, complete guarded consumption and final lazy reset compose the full private frame. -/
theorem local_match_advance_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d (min (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)))
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
      LocalState after cutoff r ds z result ∧ HeapChains after result result.strstart.toNat ∧
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
  have kept := local_prepare_match_good_at good mainChains previous length available
  have saved : HeapChainsAt hp prepared
      (min (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)) (d.strstart.toNat + d.lookahead.toNat) :=
    chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have getP : hp.bytes w = some wa := get
  have maximum := local_max_insert_nat_bounded good win get range nonempty
  obtain ⟨candidate, loopHeap, df, loopRun, goodF, chainsF, winF, bytesF, zero, startF, lookF, roomF, formF, frameF, bytesFrame, storageF, shapeF, fullF, allocF, nextF⟩ :=
    local_match_insert_loop_full_storage kept.1 saved win getP counts.2.2.1 counts.2.2.2.1
      (by rw [counts.2.2.2.2]; exact range) range
      (d.strstart + d.lookahead - MIN_MATCH_u) (by rw [maximum]; omega)
      (by intro le; apply form; rw [maximum] at le; exact le) hash_head
  have finished := local_finish_match_good_at goodF (chainsF.raise (Nat.min_le_left _ _)) winF bytesF roomF (by
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



/-- The same observed run identifies the returned private record and all
owned roots before exposing the complete storage ledger. -/
theorem local_match_advance_run_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d (min (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat - 2)))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (available : d.prev_length.toNat - 1 ≤ d.lookahead.toNat)
    (nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : d.strstart.toNat + 1 ≤ d.strstart.toNat + d.lookahead.toNat - 3 → InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) {candidate : UInt32} {after : Heap} {returned : DeflateState}
    (actual : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u)
      hash_head h = .ok (candidate,after))
    (live : DLive after r ds z returned) :
    SlowRecordFrame d returned ∧ DeflateOwned ds returned = DeflateOwned ds d ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨candidate0,after0,result,run,goodA,_chainsA,_frontier,_window,_bytes,_available,_length,_previous,
      _start,_look,_endpoint,_range,_form,_keep,_high,_allBytes,_block,_literal,_distance,record,
      _byteFrame,shape,frame,ledger,alloc,next⟩ :=
    local_match_advance_full_storage good chains win get previous length available nonempty range form hash_head
  cases Except.ok.inj (run.symm.trans actual)
  have same : result = returned := Option.some.inj (goodA.live.hs.symm.trans live.hs)
  subst returned
  refine ⟨?_,?_,shape,frame,ledger,alloc,next⟩
  · unfold SlowRecordFrame
    rw [record]
  · rw [record]
    rfl

/-- A given actual ordinary match decision has complete typed effects
on that same heap and returned state, including its original match tally.
History and packed symbols are internal caller facts; no public API domain
is changed by this observer. -/
theorem local_match_decision_run_full_storage {h after : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d returned : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat} {xs : List Symbol}
    {flush : Int32} {st next : LoopS} {hash_head : UInt32}
    (good : LocalState h cutoff r ds z d) (symbol : SymbolBoundary h ds d xs)
    (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (actual : slowDecision (some (.tab ds)) flush st hash_head h = .ok (next,after))
    (live : DLive after r ds z returned) :
    SlowRecordFrame d returned ∧ DeflateOwned ds returned = DeflateOwned ds d ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true,decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    exact Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
  have bounds := logical_previous_tally_bounds history previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  obtain ⟨pb,buf,trees,ledger,balance⟩ := symbol
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by omega
  let packed := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  obtain ⟨tallyRun,goodT,_treesT,_ledgerT,count,_nonfull,_recordT,shapeT,frameT,_liveT,allocT,nextT,
      chainsKeep,_balanceT⟩ := local_tally_match_storage good trees ledger distance length bounds.1 bounds.2.1
    (by have b := bounds.2.2.2.1; omega) room
  have chainsT : HeapChains ht dt (min (dt.strstart.toNat+1) (dt.strstart.toNat+dt.lookahead.toNat-2)) := by
    have wide : min (dt.strstart.toNat+1) (dt.strstart.toNat+dt.lookahead.toNat-2) = d.strstart.toNat+1 := by
      change min (d.strstart.toNat+1) (d.strstart.toNat+d.lookahead.toNat-2) = _
      exact Nat.min_eq_left (by omega)
    rw [wide]
    exact chainsKeep _ chains
  have getT : ht.bytes w = some wa := local_pending_window_frame good win trees.base.pbuf get packed dt
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have number := congrArg UInt32.toNat eq
    change dt.sym_next.toNat = d.sym_end.toNat at number
    rw [count] at number
    omega
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (false,ht) := by
    simpa only [flag] using tallyRun
  obtain ⟨head,other,result,advance,goodA,_chainsA,_frontier,_windowA,_bytesA,_availableA,_lengthA,_previousA,
      _start,_look,_endpoint,_rangeA,_formA,_keep,_high,_allBytes,_block,_literal,_distance,record,
      _byteFrame,shapeA,fullA,_liveA,allocA,nextA⟩ :=
    local_match_advance_full_storage goodT chainsT win getT previous history.1
      (by have b := bounds.2.2.2.2; exact b) (by change 3 ≤ d.strstart.toNat+d.lookahead.toNat;omega)
      range (fun _ => form) hash_head
  have advance' : slowMatchAdvance (some (.tab ds)) (d.strstart+d.lookahead-MIN_MATCH_u)
      hash_head ht = .ok (head,other) := advance
  have tested : slowDecision (some (.tab ds)) flush st hash_head h =
      .ok ({st with hash_head := head,bflush := false},other) := by
    dsimp only [distance,length] at tally
    unfold slowDecision
    simp only [bind_app,ldDeflateState_tab good.live.hs,selected,ite_true,tally]
    change (do
      let head ← slowMatchAdvance (some (.tab ds)) (d.strstart+d.lookahead-MIN_MATCH_u) hash_head
      pure {st with hash_head := head,bflush := false}) ht = _
    rw [bind_app,advance']
    rfl
  cases Except.ok.inj (tested.symm.trans actual)
  have same : result = returned := Option.some.inj (goodA.live.hs.symm.trans live.hs)
  subst returned
  have tallyFrame : Frame h ht (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    apply full_frame_weaken frameT
    intro b atRoot
    rcases atRoot with stateRoot | pendingRoot
    · exact Or.inr (Or.inl stateRoot)
    · subst b
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have full : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_trans_shape tallyFrame fullA shapeT
  have shape := shapeT.trans shapeA
  refine ⟨?_,?_,shape,full,full_shape_live_change shape,allocA.trans allocT,nextA.trans nextT⟩
  · unfold SlowRecordFrame
    rw [record]
    rfl
  · rw [record]
    rfl

end ZlibF.Spec.Public.Proofs.CompressLocalMatchFullStorage
