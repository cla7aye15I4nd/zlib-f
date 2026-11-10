import ZlibF.Proof.«deflate.c.engine.common-fast-insert-step»
import ZlibF.Proof.«deflate.c.engine.match-insert-loop»

/-! # The actual fast insertion do-loop terminates with exact position and storage -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
/-- The actual fast do-while inserts each consumed match position. Its rank
is the positive match_length counter stored in the real heap. At most 257
iterations run. The returned state has zero counter, the exact consumed
position, unchanged lookahead and a rolling hash ready for the next byte.
-/
theorem fast_match_insert_loop_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.match_length.toNat) (countBound : d.match_length.toNat ≤ 257)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) hash_head h =
        .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧ result.lookahead = d.lookahead ∧
      result.strstart.toNat + 1 + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧
      FastInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let total := d.strstart.toNat + d.match_length.toNat
  let Inv : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    1 ≤ state.match_length.toNat ∧ state.match_length.toNat ≤ 257 ∧
    3 ≤ state.lookahead.toNat ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + state.match_length.toNat = total ∧
    state.strstart.toNat + state.match_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    FastInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let Q : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧ state.match_length = 0 ∧
    state.strstart.toNat = total ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    FastInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let rank : UInt32 → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.match_length.toNat)).getD 0
  have step : ∀ hh heap, Inv hh heap → ∃ hh1 h1 c hh2 h2,
      fastInsertBody (some (.tab ds)) hh heap = .ok (hh1, h1) ∧
      fastInsertCond (some (.tab ds)) hh1 h1 = .ok ((c, hh2), h2) ∧
      (c = false → Q hh2 h2) ∧ (c = true → Inv hh2 h2 ∧ rank hh2 h2 < rank hh heap) := by
    intro hh heap inv
    obtain ⟨state, goodS, chainsS, winS, bytesS, posS, boundS, lookS, lookEq, sumS, roomS, formS, frameS, byteFrame, storageS, shapeS, fullS, allocS, nextS⟩ := inv
    obtain ⟨key, candidate, mid, after, bodyRun, condRun, goodA, chainsA, bytesA, startA, countA, formA, _localFrame, bytesEq, storageA, shapeA, fullA, allocA, nextA⟩ :=
      fast_match_insert_step_full_storage goodS chainsS winS bytesS posS lookS roomS formS hh
    let result := fastCountDown { bumpStart state with ins_h := key }
    have sumA : result.strstart.toNat + result.match_length.toNat = total := by rw [startA, countA]; omega
    have roomA : result.strstart.toNat + result.match_length.toNat + 1 + result.lookahead.toNat ≤
        result.window_size.toNat := by
      change result.strstart.toNat + result.match_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat
      rw [startA, countA]
      omega
    have owned : DeflateOwned ds state = DeflateOwned ds d := by rw [frameS]; rfl
    rw [owned] at fullA
    have shape := shapeS.trans shapeA
    have full := full_frame_trans_shape fullS fullA shapeS
    refine ⟨candidate, mid, result.match_length != 0, candidate, after, bodyRun, condRun, ?_, ?_⟩
    · intro stop
      have zero : result.match_length = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      refine ⟨result, goodA, chainsA, winS, bytesA, zero, ?_, lookEq, ?_, formA, fast_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA, shape, full, allocA.trans allocS, nextA.trans nextS⟩
      · have value : result.match_length.toNat = 0 := by rw [zero]; rfl
        omega
      · have value : result.match_length.toNat = 0 := by rw [zero]; rfl
        omega
    · intro more
      have nonzero : result.match_length ≠ 0 := by simpa only [bne_iff_ne] using more
      have positiveA : 1 ≤ result.match_length.toNat := by
        have ne : result.match_length.toNat ≠ 0 := by intro eq; exact nonzero (UInt32.toNat_inj.mp eq)
        omega
      refine ⟨⟨result, goodA, chainsA, winS, bytesA, positiveA, ?_, lookS, lookEq, sumA, roomA, formA, fast_insert_frame_step frameS key, bytesEq.trans byteFrame, storageS.trans storageA, shape, full, allocA.trans allocS, nextA.trans nextS⟩, ?_⟩
      · rw [countA]
        omega
      · have stateA : after.dstates ds = some result := goodA.live.hs
        simp only [rank, goodS.live.hs, stateA, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv hash_head h :=
    ⟨d, good, chains, win, get, positive, countBound, lookahead, rfl, rfl, room, form, rfl, rfl, ByteFrame.refl h _,
      Shape.refl h, (full_storage_refl h _).2.1, rfl, rfl⟩
  have fuelBound : rank hash_head h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.match_length.toNat < 18446744073709551616
    omega
  obtain ⟨candidate, after, run, result, post⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨candidate, after, result, run, post⟩


end Zlib.Deflate.Engine.Proofs
