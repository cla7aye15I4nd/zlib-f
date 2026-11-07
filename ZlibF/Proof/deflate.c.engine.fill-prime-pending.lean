import ZlibF.Proof.«deflate.c.engine.fill-insert-loop»

/-! # Complete source priming with deferred insertions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

set_option maxHeartbeats 2500000 in
/-- The full real priming fragment works for every insert<=strstart.
It retains the lower hash frontier until each pending string is inserted.
The returned insert count is exactly min(old insert, 2-lookahead).
When at least three input bytes remain, all deferred insertions are done
and the rolling hash is ready at the actual current position.
-/
theorem fill_prime_pending {h : Heap} {r : ZStreamRef} {ds w : Nat}
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
        InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h) := by
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
    obtain ⟨final, after, result, loop, goodA, chainsA, bytesA, frameA, cursorA, countA, formA⟩ :=
      fill_insert_loop str goodS chainsS win get range cursor ready formS
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
    refine ⟨after, result, ?_, goodA, ?_, bytesA, frame, countA, ?_⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, if_true]
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
    refine ⟨h, d, ?_, good, chains, rfl, rfl, ?_, ?_⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, if_false, pure_app]
    · omega
    · intro large
      omega

end Zlib.Deflate.Engine.Proofs
