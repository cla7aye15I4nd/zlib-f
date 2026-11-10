import ZlibF.Proof.«deflate.c.engine.common-fast-insert-advance»
import ZlibF.Proof.«deflate.c.life.reset»

/-! # Actual immediate-match consumption through the fast insertion branch -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Canonical state after the two actual stores before the fast
insertion loop. The source theorem below executes the stores in order. -/
def fastPrepareInsert (d : DeflateState) : DeflateState :=
  {d with lookahead := d.lookahead - d.match_length, match_length := d.match_length - 1}

theorem fast_prepare_insert_counts (d : DeflateState)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (remaining : d.match_length.toNat + 3 ≤ d.lookahead.toNat) :
    (fastPrepareInsert d).lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧
    (fastPrepareInsert d).match_length.toNat = d.match_length.toNat - 1 ∧
    3 ≤ (fastPrepareInsert d).lookahead.toNat ∧
    1 ≤ (fastPrepareInsert d).match_length.toNat ∧ (fastPrepareInsert d).match_length.toNat ≤ 257 := by
  have look : (fastPrepareInsert d).lookahead.toNat = d.lookahead.toNat - d.match_length.toNat := by
    change (d.lookahead - d.match_length).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]
  have count : (fastPrepareInsert d).match_length.toNat = d.match_length.toNat - 1 := u32_sub_one (by omega)
  exact ⟨look, count, by omega, by omega, by omega⟩

/-- Consuming the whole match retains every published old hash key.
Three remaining bytes make the reduced valid-data endpoint large enough
for those keys; this is derived, not an assumed insertion contract. -/
theorem fast_prepare_insert_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (remaining : d.match_length.toNat + 3 ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat) :
    DGood (setD h ds (fastPrepareInsert d)) r ds z (fastPrepareInsert d) ∧
      HeapChains (setD h ds (fastPrepareInsert d)) (fastPrepareInsert d) (d.strstart.toNat + 1) ∧
      (fastPrepareInsert d).strstart.toNat + (fastPrepareInsert d).match_length.toNat + 1 +
        (fastPrepareInsert d).lookahead.toNat ≤ (fastPrepareInsert d).window_size.toNat := by
  have counts := fast_prepare_insert_counts d selected bounded remaining
  have inv : DStInv h ds (fastPrepareInsert d) :=
    {good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := fastPrepareInsert d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
    exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq,
      chains_restrict H (by change d.strstart.toNat + 1 + 2 ≤ d.strstart.toNat + _; omega)⟩
  · change d.strstart.toNat + (fastPrepareInsert d).match_length.toNat + 1 +
      (fastPrepareInsert d).lookahead.toNat ≤ d.window_size.toNat
    rw [counts.1, counts.2.1]
    dsimp only [fillEnd] at range
    omega

/-- The real lookahead store, counter decrement, do-loop and final
position store consume the whole selected match. The final input
endpoint is unchanged, the fast match counter is zero and the rolling
hash is ready at the next position. All private heap effects refer to
this same source execution. The public branch guard is composed later. -/
theorem fast_match_inserting_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (remaining : d.match_length.toNat + 3 ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (head : UInt32) :
    ∃ candidate after result,
      (do wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
          wr (some (.tab ds)) (fun d => {d with match_length := d.match_length - 1})
          let hh ← cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) head
          wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1})
          pure hh) h = .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have counts := fast_prepare_insert_counts d selected bounded remaining
  obtain ⟨goodP, chainsP, roomP⟩ := fast_prepare_insert_good good chains selected bounded remaining range
  let prepared := fastPrepareInsert d
  let hp := setD h ds prepared
  obtain ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, zeroA, startA, lookA,
      endA, formA, fieldsA, bytesEqA, storageA, shapeA, fullA, _liveA, allocA, nextA⟩ :=
    fast_match_insert_advance_full_storage goodP chainsP win get counts.2.2.2.1 counts.2.2.2.2
      counts.2.2.1 roomP form head
  have source : (do
      wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
      wr (some (.tab ds)) (fun d => {d with match_length := d.match_length - 1})
      let hh ← cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) head
      wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1})
      pure hh) h = (do
        let hh ← cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) head
        wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1})
        pure hh) hp := by
    simp only [bind_app, wrD_eq, good.live.hs, setD_dstates_same, setD_setD]
    rfl
  have start : result.strstart.toNat = d.strstart.toNat + d.match_length.toNat := by
    have startCount : result.strstart.toNat = d.strstart.toNat + prepared.match_length.toNat + 1 := startA
    have count : prepared.match_length.toNat = d.match_length.toNat - 1 := counts.2.1
    omega
  have look : result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat := by rw [lookA]; exact counts.1
  have fields : result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} := by
    change result = {prepared with strstart := result.strstart, ins_h := result.ins_h, match_length := result.match_length} at fieldsA
    rw [zeroA] at fieldsA
    exact fieldsA
  have shapeP := shape_setD good.live.hs prepared
  have fullP : Frame h hp (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds prepared) (fun _ same => Or.inr (Or.inl same))
  have shape := shapeP.trans shapeA
  refine ⟨candidate, after, result, source.trans run, goodA, chainsA, winA, bytesA, zeroA,
    start, look, ?_, formA, fields, bytesEqA,
    (byte_frame_setD h ds prepared).trans storageA, shape,
    full_frame_trans_shape fullP fullA shapeP, full_shape_live_change shape, allocA, nextA⟩
  dsimp only [fillEnd]
  rw [start, look]
  omega

end Zlib.Deflate.Engine.Proofs
