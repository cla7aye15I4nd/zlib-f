import ZlibF.Proof.«deflate.c.engine.insert-full-storage»

/-! # The actual pending insertion loop and hash seeding frame -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

set_option maxHeartbeats 2000000 in
/-- The actual complete pending-insertion loop retains all old slots
outside the private footprint and leaves both allocation counters exact. -/
theorem fill_insert_loop_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32)
    (good : DGood h r ds z d) (chains : HeapChains h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ final after result,
      cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false) h =
        .ok (final, after) ∧
      DGood after r ds z result ∧ HeapChains after result final.1.toNat ∧ after.bytes = h.bytes ∧
      PendingInsertFrame d result ∧ final.1.toNat + result.insert.toNat = d.strstart.toNat ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) final.1.toNat result.ins_h ∧ ByteFrame h after (fun i => i = ds) ∧ Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let Inv : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state pos.1.toNat ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    state.strstart.toNat + state.lookahead.toNat ≤ state.window_size.toNat ∧
    pos.1.toNat + state.insert.toNat = state.strstart.toNat ∧
    state.insert.toNat ≤ d.insert.toNat ∧ 2 ≤ state.lookahead.toNat + state.insert.toNat ∧
    pos.2 = decide (state.lookahead.toNat + state.insert.toNat < 3) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧
    PendingInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let Q : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state pos.1.toNat ∧ heap.bytes = h.bytes ∧
    PendingInsertFrame d state ∧ pos.1.toNat + state.insert.toNat = d.strstart.toNat ∧
    state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let rank : (UInt32 × Bool) → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.insert.toNat)).getD 0
  have step : ∀ pos heap, Inv pos heap → ∃ c pos1 heap1,
      fillInsertCond (some (.tab ds)) pos heap = .ok ((c, pos1), heap1) ∧
      (c = false → Q pos1 heap1) ∧
      (c = true → ∃ pos2 heap2, fillInsertBody (some (.tab ds)) pos1 heap1 = .ok (pos2, heap2) ∧
        Inv pos2 heap2 ∧ rank pos2 heap2 < rank pos heap) := by
    intro pos heap inv
    obtain ⟨state, goodS, chainsS, winS, getS, rangeS, cursorS, boundS, lowerS, stopS, formS, frameS, bytesS, storageS, shapeS, fullS, allocS, nextS⟩ := inv
    have startS : state.strstart = d.strstart := congrArg (·.strstart) frameS
    have lookS : state.lookahead = d.lookahead := congrArg (·.lookahead) frameS
    refine ⟨state.insert != 0 && !pos.2, pos, heap, ?_, ?_, ?_⟩
    · simp only [fillInsertCond, bind_app, rdD_eq, goodS.live.hs, pure_app]
    · intro stopped
      have exit : state.insert.toNat = 0 ∨ state.lookahead.toNat + state.insert.toNat < 3 := by
        by_cases zero : state.insert = 0
        · left; rw [zero]; rfl
        · right
          have flag : pos.2 = true := by
            simpa [bne_iff_ne, zero] using stopped
          rw [stopS] at flag
          exact of_decide_eq_true flag
      have count : state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) := by
        rw [lookS] at lowerS exit
        rcases exit with zero | small <;> omega
      exact ⟨state, goodS, chainsS, bytesS, frameS, by rw [startS] at cursorS; exact cursorS, count, formS, storageS, shapeS, fullS, allocS, nextS⟩
    · intro continued
      have guard := continued
      simp only [Bool.and_eq_true, bne_iff_ne] at guard
      have positive : 1 ≤ state.insert.toNat := by
        have ne : state.insert.toNat ≠ 0 := by intro eq; exact guard.1 (UInt32.toNat_inj.mp eq)
        omega
      have readyS : 3 ≤ state.lookahead.toNat + state.insert.toNat := by
        have falseFlag : pos.2 = false := by
          cases bit : pos.2
          · rfl
          · have impossible : False := by simpa [bit] using guard.2
            cases impossible
        have flag : decide (state.lookahead.toNat + state.insert.toNat < 3) = false :=
          stopS.symm.trans falseFlag
        have notLow := of_decide_eq_false flag
        omega
      obtain ⟨key, after, bodyRun, goodA, chainsA, bytesA, next, countA, formA, storageA, shapeA, fullA, _liveA, allocA, nextA⟩ :=
        fill_insert_step_full_storage pos.1 pos.2 goodS chainsS winS getS rangeS cursorS positive readyS formS
      let result := pendingInsertState state key
      let stopped : Bool := decide (result.lookahead + result.insert < MIN_MATCH_u)
      let nextPos := (pos.1 + 1, stopped)
      have cursorA : nextPos.1.toNat + result.insert.toNat = result.strstart.toNat := by
        change (pos.1 + 1).toNat + result.insert.toNat = state.strstart.toNat
        rw [next, countA]
        omega
      have rangeA : result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat := rangeS
      have getA : after.bytes w = some wa := by rw [bytesA]; exact getS
      have sum := pending_sum_nat goodA winS getA rangeA (by omega : result.insert.toNat ≤ result.strstart.toNat)
      change (result.lookahead + result.insert).toNat = result.lookahead.toNat + result.insert.toNat at sum
      have stopA : nextPos.2 = decide (result.lookahead.toNat + result.insert.toNat < 3) := by
        change decide (result.lookahead + result.insert < MIN_MATCH_u) = _
        simp only [UInt32.lt_iff_toNat_lt, sum, show MIN_MATCH_u.toNat = 3 from rfl]
      have ownedS : DeflateOwned ds state = DeflateOwned ds d := by
        rw [show state = {d with ins_h := state.ins_h, insert := state.insert} from frameS]
        rfl
      have fullA' : Frame heap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        rw [← ownedS]
        exact fullA
      have fullNext := full_frame_trans_shape fullS fullA' shapeS
      refine ⟨nextPos, after, bodyRun, ⟨result, goodA, ?_, winS, getA, rangeA, cursorA, ?_, ?_, stopA,
        ?_, pending_insert_frame_step frameS key, bytesA.trans bytesS, storageS.trans storageA, shapeS.trans shapeA, fullNext, allocA.trans allocS, nextA.trans nextS⟩, ?_⟩
      · change HeapChains after result (pos.1 + 1).toNat
        rw [next]
        exact chainsA
      · rw [countA]
        omega
      · change 2 ≤ state.lookahead.toNat + result.insert.toNat
        rw [countA]
        omega
      · change InsHForm result.hash_shift result.hash_mask (bfn wa) (pos.1 + 1).toNat result.ins_h
        rw [next]
        exact formA
      · simp only [rank, goodS.live.hs, goodA.live.hs, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv (str, false) h :=
    ⟨d, good, chains, win, get, range, cursor, Nat.le_refl _, by omega,
      by simp [show ¬ d.lookahead.toNat + d.insert.toNat < 3 by omega], form, rfl, rfl, ByteFrame.refl h _, Shape.refl h,
      ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩
  have extent := window_extent good win get
  have bound : rank (str, false) h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.insert.toNat < 18446744073709551616
    omega
  obtain ⟨final, after, run, result, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩ :=
    while_heap_rank Inv rank Q step initial bound
  exact ⟨final, after, result, run, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩

set_option maxHeartbeats 2500000 in
/-- Actual hash seeding and the complete insertion loop preserve the
full private footprint, all live objects and both allocation counters. -/
theorem fill_prime_pending_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat - d.insert.toNat))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (pending : d.insert.toNat ≤ d.strstart.toNat) :
    ∃ after result,
      fillPrime (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z result ∧
      HeapChains after result (result.strstart.toNat - result.insert.toNat) ∧
      after.bytes = h.bytes ∧ PendingInsertFrame d result ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      (3 ≤ result.lookahead.toNat → result.insert = 0 ∧
        InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h) ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have extent := window_extent good win get
  have sum := pending_sum_nat good win get range pending
  let str := d.strstart - d.insert
  have position : str.toNat = d.strstart.toNat - d.insert.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr pending)
  have cursor : str.toNat + d.insert.toNat = d.strstart.toNat := by omega
  by_cases enter : d.lookahead + d.insert ≥ MIN_MATCH_u
  · have ready : 3 ≤ d.lookahead.toNat + d.insert.toNat := by
      have guard := UInt32.le_iff_toNat_le.mp enter
      rw [sum] at guard
      exact guard
    have fit : str.toNat + 2 ≤ wa.size := by omega
    let seeded := insertSeedState d wa str
    let hs := setD h ds seeded
    have params : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters good.inv
    have inv : DStInv h ds seeded :=
      { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
    have goodS : DGood hs r ds z seeded := good.setD' rfl good.live.status inv (by trkeep)
    have chainsS : HeapChains hs seeded str.toNat := by
      obtain ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩ := chains
      rw [← position] at H
      exact ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩
    have formS : InsHForm seeded.hash_shift seeded.hash_mask (bfn wa) str.toNat seeded.ins_h :=
      insert_seed_form (d := d) params fit
    have seedRun : fillInsertSeed (some (.tab ds)) d.window str h = .ok ((), hs) :=
      fill_insert_seed_run good.live.hs win get str fit (by omega) (by
        rw [UInt32.lt_iff_toNat_lt]
        exact (hash_parameters good.inv).hsh_lt)
    obtain ⟨final, after, result, loop, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩ :=
      fill_insert_loop_full_storage str goodS chainsS win get range cursor ready formS
    have frame : PendingInsertFrame d result := by
      unfold PendingInsertFrame at frameA ⊢
      rw [frameA]
      rfl
    have startA : result.strstart = d.strstart := congrArg (·.strstart) frame
    have lookA : result.lookahead = d.lookahead := congrArg (·.lookahead) frame
    have frontier : final.1.toNat = result.strstart.toNat - result.insert.toNat := by
      change final.1.toNat + result.insert.toNat = d.strstart.toNat at cursorA
      rw [startA]
      omega
    have owned : DeflateOwned ds seeded = DeflateOwned ds d := rfl
    have seedShape := shape_setD good.live.hs seeded
    have seedFrame : Frame h hs (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
      full_frame_weaken (state_store_full_frame h ds seeded) (fun _ same => Or.inr (Or.inl same))
    have loopFrame : Frame hs after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      rw [← owned]
      exact fullA
    have full := full_frame_trans_shape seedFrame loopFrame seedShape
    refine ⟨after, result, ?_, goodA, ?_, bytesA, frame, countA, ?_,
      (byte_frame_setD h ds seeded).trans storageA, seedShape.trans shapeA, full, allocA, nextA⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, ite_true]
      change (do
        fillInsertSeed (some (.tab ds)) d.window str
        let (_, _) ← cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false)
        pure ()) h = _
      simp only [bind_app, seedRun, loop, pure_app]
    · rw [← frontier]
      exact chainsA
    · intro large
      have zeroNat : result.insert.toNat = 0 := by
        change result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) at countA
        rw [lookA] at large
        omega
      have zero : result.insert = 0 := UInt32.toNat_inj.mp zeroNat
      refine ⟨zero, ?_⟩
      have finalPosition : final.1.toNat = result.strstart.toNat := by rw [frontier, zeroNat, Nat.sub_zero]
      rw [← finalPosition]
      exact formA
  · have small : d.lookahead.toNat + d.insert.toNat < 3 := by
      have guard : ¬ MIN_MATCH_u.toNat ≤ (d.lookahead + d.insert).toNat := by
        intro ge
        exact enter (UInt32.le_iff_toNat_le.mpr ge)
      rw [sum] at guard
      change ¬ 3 ≤ _ at guard
      omega
    refine ⟨h, d, ?_, good, chains, rfl, rfl, ?_, ?_, ByteFrame.refl h _, Shape.refl h,
      ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, ite_false, pure_app]
    · omega
    · intro large
      omega

end Zlib.Deflate.Engine.Proofs
