import ZlibF.Proof.«compress.c.local-match-endpoint»

/-! # Actual selected-match consumption with private local representation -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchStep
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalMatchEndpoint
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {cutoff : Nat}

/-- The actual guarded source step and its saved valid endpoint admit
old caller typed collisions. Only internal local-state facts are used. -/
theorem local_match_insert_step {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
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
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) := by
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
      ByteFrame h mid (fun i => i = ds) := by
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
      obtain ⟨key, candidate, mid, run, goodI, chainsI, bytesI, formI, storageI⟩ :=
        local_current_insert_storage_at bumped.2.1 bumped.2.2 win getB ordered valid data primed
      have frontierEq : min ((bumpStart d).strstart.toNat + 1) (validEnd - 2) =
          (bumpStart d).strstart.toNat + 1 := Nat.min_eq_left (by omega)
      have frontierI : HeapChainsAt mid { bumpStart d with ins_h := key }
          (min ((bumpStart d).strstart.toNat + 1) (validEnd - 2)) validEnd := by
        rw [frontierEq]; exact chainsI
      refine ⟨key, candidate, mid, ?_, goodI, frontierI, bytesI, fun _ => formI,
        (byte_frame_setD h ds (bumpStart d)).trans storageI⟩
      rw [source]
      simp only [bind_app, rdD_eq, stateB, guard, ite_true]
      exact run
    · have keep : { bumpStart d with ins_h := d.ins_h } = bumpStart d := rfl
      have later : ¬ (bumpStart d).strstart.toNat + 1 ≤ max_insert.toNat := by
        have bound : ¬ (bumpStart d).strstart.toNat ≤ max_insert.toNat := by
          intro le; exact guard (UInt32.le_iff_toNat_le.mpr le)
        omega
      refine ⟨d.ins_h, hash_head, hb, ?_, bumped.2.1,
        bumped.2.2.raise (by have ss := bumped.1; omega), rfl, ?_, byte_frame_setD h ds (bumpStart d)⟩
      · rw [source]
        simp only [bind_app, rdD_eq, stateB, guard, ite_false]
        rfl
      · intro le; exact False.elim (later le)
  obtain ⟨key, candidate, mid, bodyRun, goodI, chainsI, bytesI, formI, storageI⟩ := body
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
  exact ⟨key, candidate, mid, after, bodyRun, condition, kept.1, kept.2,
    by change mid.bytes w = some wa; rw [bytesI]; exact get,
    ss, count, formI, bytesI,
    storageI.trans (byte_frame_setD mid ds (countDown di))⟩

end ZlibF.Spec.Public.Proofs.CompressLocalMatchStep
