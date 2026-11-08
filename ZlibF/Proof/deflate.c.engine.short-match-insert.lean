import ZlibF.Proof.«deflate.c.engine.match-endpoint»

/-! # Guarded match consumption through the saved endpoint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A consumed position is inserted only when its three real bytes lie
below the original endpoint. The short-input skip follows the same C
branch and retains the previous candidate and rolling key. -/
theorem slow_match_insert_step_at {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d)
    (chains : HeapChainsAt h d (d.strstart.toNat + 1) validEnd)
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
      DGood after r ds z result ∧ HeapChainsAt after result (result.strstart.toNat + 1) validEnd ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.prev_length.toNat = d.prev_length.toNat - 1 ∧
      (result.strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h) ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) := by
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
        ((bumpStart d).strstart.toNat + 1) validEnd ∧ mid.bytes = h.bytes ∧
      ((bumpStart d).strstart.toNat + 1 ≤ max_insert.toNat →
        InsHForm d.hash_shift d.hash_mask (bfn wa) ((bumpStart d).strstart.toNat + 1) key) ∧
      ByteFrame h mid (fun i => i = ds) := by
    by_cases guard : (bumpStart d).strstart ≤ max_insert
    · have ordered : d.strstart.toNat + 1 ≤ (bumpStart d).strstart.toNat := by rw [bumped.1]; exact Nat.le_refl _
      have data : (bumpStart d).strstart.toNat + 3 ≤ validEnd := by
        have bound := UInt32.le_iff_toNat_le.mp guard
        omega
      have primed : InsHForm (bumpStart d).hash_shift (bumpStart d).hash_mask (bfn wa)
          (bumpStart d).strstart.toNat (bumpStart d).ins_h := by
        change InsHForm d.hash_shift d.hash_mask (bfn wa) (bumpStart d).strstart.toNat d.ins_h
        rw [bumped.1]
        exact form (by have bound := UInt32.le_iff_toNat_le.mp guard; rw [bumped.1] at bound; exact bound)
      obtain ⟨key, candidate, mid, run, goodI, chainsI, bytesI, formI, storageI⟩ :=
        current_insert_storage_at bumped.2.1 bumped.2.2 win getB ordered valid data primed
      refine ⟨key, candidate, mid, ?_, goodI, chainsI, bytesI, fun _ => formI,
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
        bumped.2.2.raise (by omega), rfl, ?_, byte_frame_setD h ds (bumpStart d)⟩
      · rw [source]
        simp only [bind_app, rdD_eq, stateB, guard, ite_false]
        rfl
      · intro le; exact False.elim (later le)
  obtain ⟨key, candidate, mid, bodyRun, goodI, chainsI, bytesI, formI, storageI⟩ := body
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
  exact ⟨key, candidate, mid, after, bodyRun, condition, kept.1, kept.2,
    by change mid.bytes w = some wa; rw [bytesI]; exact get,
    ss, count, formI, bytesI,
    storageI.trans (byte_frame_setD mid ds (countDown di))⟩

end Zlib.Deflate.Engine.Proofs
