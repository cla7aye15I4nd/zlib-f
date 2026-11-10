import ZlibF.Proof.«deflate.c.engine.common-fast-insert-loop»

/-! # The actual fast insertion branch finishes at the next input position -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual do-loop followed by its final strstart++ ends with the
fast counter zero and a hash seed for the new current position. The
returned heap and every private resource effect are those of the same
actual source execution, rather than a slow-loop surrogate. -/
theorem fast_match_insert_advance_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.match_length.toNat) (countBound : d.match_length.toNat ≤ 257)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (head : UInt32) :
    ∃ candidate after result,
      (do let hh ← cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) head
          wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1})
          pure hh) h = .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat + 1 ∧
      result.lookahead = d.lookahead ∧ fillEnd result = d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      FastInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨candidate, middle, state, run, goodM, chainsM, winM, bytesM, zeroM, startM, lookM,
      roomM, formM, fieldsM, bytesEqM, storageM, shapeM, fullM, allocM, nextM⟩ :=
    fast_match_insert_loop_full_storage good chains win get positive countBound lookahead room form head
  have bumped := bump_start_good goodM chainsM winM bytesM roomM
  let result := bumpStart state
  let after := setD middle ds result
  have startA : result.strstart.toNat = d.strstart.toNat + d.match_length.toNat + 1 := by
    rw [bumped.1, startM]
  have chainsA : HeapChains after result result.strstart.toNat := by
    rw [bumped.1]
    exact bumped.2.2.1
  have fieldsA : FastInsertFrame d result := by
    dsimp only [result]
    unfold FastInsertFrame at fieldsM ⊢
    rw [fieldsM]
    rfl
  have shapeA := shape_setD goodM.live.hs result
  have fullA : Frame middle after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame middle ds result) (fun _ same => Or.inr (Or.inl same))
  have shape := shapeM.trans shapeA
  refine ⟨candidate, after, result, ?_, bumped.2.1, chainsA, winM, bytesM, zeroM,
    startA, lookM, ?_, ?_, fieldsA, bytesEqM, storageM.trans (byte_frame_setD middle ds result),
    shape, full_frame_trans_shape fullM fullA shapeM, full_shape_live_change shape, allocM, nextM⟩
  · rw [bind_app, run]
    have write : wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1}) middle = .ok ((), after) := by
      simp [wrD_eq, goodM.live.hs, after, result, bumpStart]
    simp only [bind_app, write, pure_app]
  · change result.strstart.toNat + state.lookahead.toNat = _
    rw [startA, lookM]
  · change InsHForm state.hash_shift state.hash_mask (bfn wa) result.strstart.toNat state.ins_h
    rw [bumped.1]
    exact formM

end Zlib.Deflate.Engine.Proofs
