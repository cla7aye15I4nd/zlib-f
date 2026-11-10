import ZlibF.Proof.«deflate.c.engine.common-fast-search-source»

/-! # Actual insertion supplies the fast matcher's premises -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- With three real key bytes, actual insertion establishes the published
chain and the guarded fast search returns a current-position match witness.
The initialized short length handles inactive searches. All input bytes,
caller objects and allocation counters retain their exact frames. -/
theorem fast_search_room_full_storage {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (previous : d.prev_length = 2) (length : d.match_length.toNat ≤ 2)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      fastSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      DGood after r ds z (matchState { d with ins_h := key } pos len) ∧
      HeapChains after (matchState { d with ins_h := key } pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → len.toNat ≤ d.lookahead.toNat ∧
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, keyBound, hash, inserted, goodI, chainsI, older, published, linked⟩ :=
    insert_published_three good env chains ordered range lookahead form
  let di := { d with ins_h := key }
  let hi := insertedHeap h ds p q d pa qa key
  let prev := pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat)
  let head := qa.set! key.toNat d.strstart.toUInt16
  let candidate := (wfn qa key.toNat).toUInt32
  have getW : hi.bytes w = some wa := by simpa only [hi, insertedHeap] using env.wbytes
  have getP : hi.words p = some prev := by simp [hi, prev, insertedHeap, env.hne.symm]
  have getQ : hi.words q = some head := by simp [hi, head, insertedHeap]
  have actualChains := heap_chains_arrays chainsI
    (by simpa only [di] using env.win)
    (by simpa only [di] using env.prevp)
    (by simpa only [di] using env.headp) getW getP getQ
  have originalHash : (hkey di.hash_shift di.hash_mask (bfn wa) di.strstart.toNat).toNat = key.toNat := by
    change (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key.toNat
    rw [hash]
  obtain ⟨after, pos, len, findRun, goodF, chainsF, lenBound, evidence, bytesF, _wordsF, storageF, shapeF, fullF, _liveF, allocF, nextF⟩ := fast_find_room_full_storage goodI chainsI
    (by simpa only [di] using env.win)
    (by simpa only [di] using env.prevp)
    (by simpa only [di] using env.headp)
    getW getP getQ actualChains originalHash keyBound published linked
    (by intro nz; apply older; simpa only [candidate, UInt16.toNat_toUInt32] using
      (show candidate.toNat ≠ 0 from fun eq => nz (UInt32.toNat_inj.mp eq)))
    range room previous length
  have ready : d.lookahead ≥ MIN_MATCH_u := by
    change MIN_MATCH_u ≤ d.lookahead
    rw [UInt32.le_iff_toNat_le]
    change 3 ≤ d.lookahead.toNat
    omega
  have frame : after.bytes = h.bytes := by
    calc after.bytes = hi.bytes := bytesF
         _ = h.bytes := rfl
  have nextForm : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key := by
    rw [hash, ← hkey_of_form env.params form]
    exact form_next form
  have insertedFrame : ByteFrame h hi (fun i => i = ds) := by
    exact ⟨rfl, fun _ _ => rfl,
      fun i outside => by simp [hi, insertedHeap, upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
  have stored : ByteFrame h after (fun i => i = ds) := insertedFrame.trans storageF
  have extent := window_extent good env.win env.wbytes
  obtain ⟨shapeI, fullI, _liveI, allocI, nextI⟩ :=
    insert_string_run_full_storage good env d.strstart (by omega) (by omega) inserted
  have fullF' : Frame hi after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken fullF (fun _ same => Or.inr (Or.inl same))
  have shape := shapeI.trans shapeF
  have full := full_frame_trans_shape fullI fullF' shapeI
  refine ⟨key, after, pos, len, ?_, goodF, chainsF, lenBound, evidence, frame, nextForm,
    stored, shape, full, full_shape_live_change shape, allocF.trans allocI, nextF.trans nextI⟩
  unfold fastSearch
  simp only [bind_app, rdD_eq, good.live.hs, ready, if_true, inserted]
  simp only [findRun]
  rfl

end Zlib.Deflate.Engine.Proofs
