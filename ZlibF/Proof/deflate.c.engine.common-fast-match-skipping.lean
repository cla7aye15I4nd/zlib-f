import ZlibF.Proof.«deflate.c.engine.full-storage»
import ZlibF.Proof.«deflate.c.engine.short-search-frontier»

/-! # Actual fast match consumption when repeated insertion is skipped -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Canonical state of the actual lookahead and skipped-position stores. -/
def fastSkipState (d : DeflateState) : DeflateState :=
  {d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0}

/-- The real skipped-insertion branch consumes the selected match and
rebuilds the hash from the next two physical window bytes. The proven
comparison margin reserves those reads even at EOF. Hash frontiers are
raised without claiming that skipped positions were inserted. No new
input or output, byte changes, allocations or frees occur here. -/
theorem fast_match_skipping_frontier_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (consumed : d.match_length.toNat ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ after result,
      (do wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
          wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0})
          let next ← ldDeflateState (some (.tab ds))
          fillInsertSeed (some (.tab ds)) next.window next.strstart) h = .ok ((), after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧ EndFrontier after result ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} ∧
      after.bytes = h.bytes ∧ after.words = h.words ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have extent := window_extent good win get
  have start : (fastSkipState d).strstart.toNat = d.strstart.toNat + d.match_length.toNat := by
    change (d.strstart + d.match_length).toNat = _
    rw [UInt32.toNat_add]
    dsimp only [fillEnd] at range
    exact Nat.mod_eq_of_lt (by omega)
  have look : (fastSkipState d).lookahead.toNat = d.lookahead.toNat - d.match_length.toNat := by
    change (d.lookahead - d.match_length).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact consumed)]
  have endpoint : fillEnd (fastSkipState d) = fillEnd d := by
    dsimp only [fillEnd]
    rw [start, look]
    omega
  have fit : (fastSkipState d).strstart.toNat + 2 ≤ wa.size := by rw [start]; omega
  let skipped := fastSkipState d
  let hs := setD h ds skipped
  let result := insertSeedState skipped wa skipped.strstart
  let after := setD h ds result
  have inv : DStInv h ds skipped :=
    {good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodS : DGood hs r ds z skipped := good.setD' rfl good.live.status inv (by trkeep)
  have seedRun : fillInsertSeed (some (.tab ds)) skipped.window skipped.strstart hs = .ok ((), after) := by
    have run := fill_insert_seed_run goodS.live.hs (show skipped.window = .ref (.blk w) 0 from win)
      (show hs.bytes w = some wa from get) skipped.strstart fit (by omega)
      (by rw [UInt32.lt_iff_toNat_lt]; exact (hash_parameters good.inv).hsh_lt)
    simpa only [hs, after, result, setD_setD] using run
  have source : (do
      wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
      wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0})
      let next ← ldDeflateState (some (.tab ds))
      fillInsertSeed (some (.tab ds)) next.window next.strstart) h =
        fillInsertSeed (some (.tab ds)) skipped.window skipped.strstart hs := by
    let looked := {d with lookahead := d.lookahead - d.match_length}
    let hl := setD h ds looked
    have first : wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length}) h = .ok ((), hl) := by
      simp [wrD_eq, good.live.hs, hl, looked]
    have second : wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0}) hl = .ok ((), hs) := by
      simp [wrD_eq, hl, looked, hs, skipped, fastSkipState, setD_setD]
    simp only [bind_app, first, second, ldDeflateState_tab goodS.live.hs]
  have invA : DStInv h ds result :=
    {good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA : DGood after r ds z result := good.setD' rfl good.live.status invA (by trkeep)
  have chainsA : HeapChains after result result.strstart.toNat := by
    obtain ⟨wb, p, q, a, pa, qa, win0, prev, head, hw, hp, hq, H⟩ := chains
    refine ⟨wb, p, q, a, pa, qa, win0, prev, head, hw, hp, hq, ?_⟩
    apply chains_mono H
    · change d.strstart.toNat + 1 ≤ (fastSkipState d).strstart.toNat
      rw [start]; omega
    · change fillEnd d ≤ fillEnd (fastSkipState d)
      rw [endpoint]
      exact Nat.le_refl _
  have endA : EndFrontier after result := by
    obtain ⟨wb, p, q, a, pa, qa, win0, prev, head, hw, hp, hq, H⟩ := chains
    refine ⟨wb, p, q, a, pa, qa, win0, prev, head, hw, hp, hq, ?_⟩
    apply chains_mono H
    · change d.strstart.toNat + 1 ≤ min (fastSkipState d).strstart.toNat (fillEnd (fastSkipState d) - 2)
      refine Nat.le_min.mpr ⟨?_, ?_⟩
      · rw [start]; omega
      · rw [endpoint]
        dsimp only [fillEnd]
        omega
    · change fillEnd d ≤ fillEnd (fastSkipState d)
      rw [endpoint]
      exact Nat.le_refl _
  have formA : InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h :=
    insert_seed_form (d := skipped) (hash_parameters goodS.inv) fit
  have fields : result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} := rfl
  have shape := shape_setD good.live.hs result
  refine ⟨after, result, source.trans seedRun, goodA, chainsA, endA, win, get, rfl,
    start, look, endpoint, formA, fields, rfl, rfl, byte_frame_setD h ds result,
    shape, ?_, full_shape_live_change shape, rfl, rfl⟩
  exact full_frame_weaken (state_store_full_frame h ds result) (fun _ same => Or.inr (Or.inl same))

/-- The earlier physical statement is the projection of the stronger
EOF-frontier and unchanged-word-array execution result. -/
theorem fast_match_skipping_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (consumed : d.match_length.toNat ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ after result,
      (do wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
          wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0})
          let next ← ldDeflateState (some (.tab ds))
          fillInsertSeed (some (.tab ds)) next.window next.strstart) h = .ok ((), after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨after, result, run, goodA, chainsA, _endA, winA, bytesA, zeroA, startA, lookA, endpoint,
      formA, fieldsA, bytesEqA, _wordsEqA, storageA, shapeA, frameA, liveA, countA, nextA⟩ :=
    fast_match_skipping_frontier_full_storage good chains win get selected bounded consumed range room
  exact ⟨after, result, run, goodA, chainsA, winA, bytesA, zeroA, startA, lookA, endpoint,
    formA, fieldsA, bytesEqA, storageA, shapeA, frameA, liveA, countA, nextA⟩

end Zlib.Deflate.Engine.Proofs
