import ZlibF.Proof.«compress.c.local-match-step»

/-! # Actual selected-match consumption with private local representation -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchLoop
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalMatchStep
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {cutoff : Nat}

/-- The actual guarded source step and its saved valid endpoint admit
old caller typed collisions. Only internal local-state facts are used. -/
theorem local_match_insert_loop {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
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
      MatchInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) := by
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
    MatchInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds)
  let Q : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    LocalState heap cutoff r ds z state ∧ HeapChainsAt heap state (min (state.strstart.toNat + 1) (validEnd - 2)) validEnd ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧ state.prev_length = 0 ∧
    state.strstart.toNat = total ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    (state.strstart.toNat + 1 ≤ max_insert.toNat →
      InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h) ∧
    MatchInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds)
  let rank : UInt32 → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.prev_length.toNat)).getD 0
  have step : ∀ hh heap, Inv hh heap → ∃ hh1 h1 c hh2 h2,
      slowMatchBody (some (.tab ds)) max_insert hh heap = .ok (hh1, h1) ∧
      slowMatchCond (some (.tab ds)) hh1 h1 = .ok ((c, hh2), h2) ∧
      (c = false → Q hh2 h2) ∧ (c = true → Inv hh2 h2 ∧ rank hh2 h2 < rank hh heap) := by
    intro hh heap inv
    obtain ⟨state, goodS, chainsS, winS, bytesS, posS, boundS, lookEq, sumS, roomS, validS, formS, frameS, byteFrame, storageS⟩ := inv
    obtain ⟨key, candidate, mid, after, bodyRun, condRun, goodA, chainsA, bytesA, startA, countA, formA, bytesEq, storageA⟩ :=
      local_match_insert_step goodS chainsS winS bytesS posS roomS validS max_insert maximum formS hh
    let result := countDown { bumpStart state with ins_h := key }
    have sumA : result.strstart.toNat + result.prev_length.toNat = total := by rw [startA, countA]; omega
    have roomA : result.strstart.toNat + result.prev_length.toNat + 1 + result.lookahead.toNat ≤
        result.window_size.toNat := by
      change result.strstart.toNat + result.prev_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat
      rw [startA, countA]
      omega
    refine ⟨candidate, mid, result.prev_length != 0, candidate, after, bodyRun, condRun, ?_, ?_⟩
    · intro stop
      have zero : result.prev_length = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      refine ⟨result, goodA, chainsA, winS, bytesA, zero, ?_, lookEq, ?_, formA, match_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA⟩
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
    · intro more
      have nonzero : result.prev_length ≠ 0 := by simpa only [bne_iff_ne] using more
      have positiveA : 1 ≤ result.prev_length.toNat := by
        have ne : result.prev_length.toNat ≠ 0 := by intro eq; exact nonzero (UInt32.toNat_inj.mp eq)
        omega
      refine ⟨⟨result, goodA, chainsA, winS, bytesA, positiveA, ?_, lookEq, sumA, roomA, validS, formA, match_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA⟩, ?_⟩
      · rw [countA]
        omega
      · have stateA : after.dstates ds = some result := goodA.live.hs
        simp only [rank, goodS.live.hs, stateA, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv hash_head h :=
    ⟨d, good, chains, win, get, positive, countBound, rfl, rfl, room, valid, form, rfl, rfl, ByteFrame.refl h _⟩
  have fuelBound : rank hash_head h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.prev_length.toNat < 18446744073709551616
    omega
  obtain ⟨candidate, after, run, result, post⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨candidate, after, result, run, post⟩


end ZlibF.Spec.Public.Proofs.CompressLocalMatchLoop
