import ZlibF.Proof.«compress.c.local-slow-find»

/-! # Actual insertion and general lazy search without global caller uniqueness -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSearch
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSlowFind
set_option autoImplicit false
set_option maxRecDepth 100000

theorem local_window_extent {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    wa.size = d.window_size.toNat ∧ d.window_size.toNat ≤ 65536 := by
  obtain ⟨w0, p, q, b, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  rw [good.inv.wsz]
  exact ⟨size, by omega⟩

theorem local_insert_published_three {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key : UInt32,
      let after := insertedHeap h ds p q d pa qa key
      let candidate := (wfn qa key.toNat).toUInt32
      let d' := { d with ins_h := key }
      key.toNat < d.hash_size.toNat ∧
      key = hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat ∧
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      LocalState after cutoff r ds z d' ∧ HeapChains after d' (d.strstart.toNat + 1) ∧
      (candidate.toNat ≠ 0 → candidate.toNat < d.strstart.toNat) ∧
      (wfn (qa.set! key.toNat d.strstart.toUInt16) key.toNat).toNat = d.strstart.toNat ∧
      (wfn (pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat))
        (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat := by
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have bound : d.strstart.toNat < 65536 := by rw [good.inv.wsz] at range; omega
  obtain ⟨wb, pb, qb, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa0, get, size⟩ := blocks.wa
  have wid : wb = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst wb
  have arr : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  have fit : d.strstart.toNat + 2 < wa.size := by rw [good.inv.wsz] at range; omega
  obtain ⟨key, eq, keyBound, run⟩ := INSERT_STRING_ok good.live.hs env d.strstart fit (by omega)
  have byte : wa[d.strstart.toNat + 2]! = bfn wa (d.strstart.toNat + 2) := by
    simp [bfn, Array.getD_eq_getD_getElem?, fit]
  have hash : key = hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat := by
    rw [eq, byte]
    exact hkey_of_form env.params form
  obtain ⟨key0, after, run0, good0, chain0, _primed, _exact⟩ := local_insert_string_chains good env chains d.strstart rfl
    good.inv.wsize good.inv.wmask ordered (by omega) (by rw [good.inv.wsz] at range; omega) bound form
  have pair := Except.ok.inj (run0.symm.trans run)
  have heapEq : after = insertedHeap h ds p q d pa qa key := congrArg Prod.snd pair
  have state := good0.live.hs
  rw [heapEq] at state
  have states : { d with ins_h := key } = { d with ins_h := key0 } := by
    exact Option.some.inj ((by simp [insertedHeap] : (insertedHeap h ds p q d pa qa key).dstates ds = some { d with ins_h := key }).symm.trans state)
  have keys : key = key0 := congrArg (·.ins_h) states
  subst key0
  rw [heapEq] at good0 chain0
  have slotBound : (d.strstart &&& d.w_mask).toNat < pa.size := by
    rw [UInt32.toNat_and]
    have bit := Nat.and_le_right (n := d.strstart.toNat) (m := d.w_mask.toNat)
    have maskBound := env.wmask
    have capacity := env.wsize
    omega
  have keyFit : key.toNat < qa.size := by have cap := env.hsize; omega
  refine ⟨key, keyBound, hash, run, good0, chain0, ?_, ?_, ?_⟩
  · intro nonzero
    have nz : (wfn qa key.toNat).toNat ≠ 0 := by simpa using nonzero
    have lt := head_lt chains keyBound nz
    simpa using (show (wfn qa key.toNat).toNat < d.strstart.toNat by omega)
  · rw [wfn_set qa _ _ keyFit]
    simp only [ite_true, UInt32.toNat_toUInt16, Nat.mod_eq_of_lt bound]
  · have mask : (d.strstart &&& d.w_mask).toNat = d.strstart.toNat &&& (d.w_size.toNat - 1) := by
      rw [UInt32.toNat_and, good.inv.wmask]
    rw [← mask, wfn_set pa _ _ slotBound]
    simp

/-- The actual lazy scalar store is local to the private state. -/
theorem local_lazy_prepare {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : LocalState h cutoff r ds z d)
    (chains : HeapChains h d top) :
    LocalState (setD h ds (lazyPrepare d)) cutoff r ds z (lazyPrepare d) ∧
      HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top := by
  exact ⟨local_state_setD good rfl good.live.status (lazy_prepare_inv good.inv) (by trkeep),
    lazy_prepare_chains chains⟩

/-- Complete actual insertion/search, including active nonzero candidates
and short-match filtering. Physical window room and hash history are
internal execution invariants; no callee contract is assumed. -/
theorem local_slow_search_room {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (length : d.match_length.toNat ≤ 258)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      LocalState after cutoff r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len) ∧
      HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧ len.toNat ≤ d.lookahead.toNat ∧
      (3 ≤ len.toNat → d.match_length.toNat < len.toNat →
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, keyBound, hash, inserted, goodI, chainsI, older, published, linked⟩ :=
    local_insert_published_three good env chains ordered range lookahead form
  let di := { d with ins_h := key }
  let hi := insertedHeap h ds p q d pa qa key
  let dm := lazyPrepare di
  let hm := setD hi ds dm
  let prev := pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat)
  let head := qa.set! key.toNat d.strstart.toUInt16
  let candidate := (wfn qa key.toNat).toUInt32
  have goodM : LocalState hm cutoff r ds z dm := (local_lazy_prepare goodI chainsI).1
  have chainsM : HeapChains hm dm (d.strstart.toNat + 1) := (local_lazy_prepare goodI chainsI).2
  have getW : hm.bytes w = some wa := by simpa only [hm, hi, setD_bytes, insertedHeap] using env.wbytes
  have getP : hm.words p = some prev := by simp [hm, hi, prev, insertedHeap, env.hne.symm]
  have getQ : hm.words q = some head := by simp [hm, hi, head, insertedHeap]
  have actualChains := heap_chains_arrays chainsM
    (by simpa only [dm, di, lazyPrepare] using env.win)
    (by simpa only [dm, di, lazyPrepare] using env.prevp)
    (by simpa only [dm, di, lazyPrepare] using env.headp) getW getP getQ
  have originalHash : (hkey dm.hash_shift dm.hash_mask (bfn wa) dm.strstart.toNat).toNat = key.toNat := by
    change (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key.toNat
    rw [hash]
  obtain ⟨after, pos, len, findRun, goodF, chainsF, lenBound, evidence, bytesF, storageF, clippedF, shapeF, fullF, _liveF, allocF, nextF⟩ := local_slow_find_room goodM chainsM
    (by simpa only [dm, di, lazyPrepare] using env.win)
    (by simpa only [dm, di, lazyPrepare] using env.prevp)
    (by simpa only [dm, di, lazyPrepare] using env.headp)
    getW getP getQ actualChains originalHash keyBound published linked
    (by intro nz; apply older; simpa only [candidate, UInt16.toNat_toUInt32] using
      (show candidate.toNat ≠ 0 from fun eq => nz (UInt32.toNat_inj.mp eq)))
    range room length (by change (2 : UInt32).toNat ≤ 258; decide)
  have ready : d.lookahead ≥ MIN_MATCH_u := by
    change MIN_MATCH_u ≤ d.lookahead
    rw [UInt32.le_iff_toNat_le]
    change 3 ≤ d.lookahead.toNat
    omega
  have frame : after.bytes = h.bytes := by
    calc after.bytes = hm.bytes := bytesF
         _ = h.bytes := rfl
  have nextForm : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key := by
    rw [hash, ← hkey_of_form env.params form]
    exact form_next form
  have insertedFrame : ByteFrame h hi (fun i => i = ds) := by
    exact ⟨rfl, fun _ _ => rfl,
      fun i outside => by simp [hi, insertedHeap, upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
  have stored : ByteFrame h after (fun i => i = ds) :=
    (insertedFrame.trans (byte_frame_setD hi ds dm)).trans storageF
  have extent := local_window_extent good env.win env.wbytes
  obtain ⟨shapeI, fullI, _liveI, allocI, nextI⟩ :=
    local_insert_string_storage good env d.strstart (by omega) (by omega) inserted
  have shapeM := shape_setD goodI.live.hs dm
  have fullM : Frame hi hm (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame hi ds dm) (fun _ same => Or.inr (Or.inl same))
  have fullF' : Frame hm after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken fullF (fun _ same => Or.inr (Or.inl same))
  have shape := (shapeI.trans shapeM).trans shapeF
  have full := full_frame_trans_shape (full_frame_trans_shape fullI fullM shapeI) fullF' (shapeI.trans shapeM)
  refine ⟨key, after, pos, len, slow_search_composes good.live.hs ready inserted findRun,
    goodF, chainsF, lenBound, clippedF lookahead (by change 2 ≤ d.lookahead.toNat; omega),
    ?_, frame, nextForm, stored, shape, full, full_shape_live_change shape, allocF.trans allocI, nextF.trans nextI⟩
  intro large longer
  rcases evidence with retained | stale | short | valid
  · have two : len = 2 := retained.1
    rw [two] at large
    change 3 ≤ 2 at large
    omega
  · change len.toNat ≤ d.match_length.toNat at stale
    omega
  · omega
  · exact valid


end ZlibF.Spec.Public.Proofs.CompressLocalSearch
