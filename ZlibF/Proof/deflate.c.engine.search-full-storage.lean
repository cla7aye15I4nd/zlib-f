import ZlibF.Proof.«deflate.c.engine.fill-full-storage»
import ZlibF.Proof.«deflate.c.engine.search-boundary»

/-! # Complete heap frames for actual lazy match search -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An unchanged heap retains its full frame and exact allocation ledger. -/
theorem full_storage_refl (h : Heap) (changed : Nat → Prop) :
    Shape h h ∧ Frame h h changed ∧ LiveChange h h (fun _ => False) (fun _ => False) ∧
      h.nalloc = h.nalloc ∧ h.nextBlk = h.nextBlk := by
  exact ⟨Shape.refl h, ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ =>
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, full_shape_live_change (Shape.refl h), rfl, rfl⟩

/-- An actual state-slot update retains all other represented objects and allocation counters. -/
theorem state_store_full_storage {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (result : DeflateState) :
    Shape h (setD h ds result) ∧ Frame h (setD h ds result) (fun b => b = ds) ∧
      LiveChange h (setD h ds result) (fun _ => False) (fun _ => False) ∧
      (setD h ds result).nalloc = h.nalloc ∧ (setD h ds result).nextBlk = h.nextBlk := by
  have shape := shape_setD state result
  exact ⟨shape, state_store_full_frame h ds result, full_shape_live_change shape, rfl, rfl⟩

/-- Actual guarded matching and its short-match filter modify only the state record. Physical comparison room is explicit. -/
theorem slow_find_room_full_storage {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : DGood h r ds z d) (heapChains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat))
    (hash : (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key)
    (keyBound : key < d.hash_size.toNat) (published : (wfn qa key).toNat = d.strstart.toNat)
    (link : (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat)
    (older : candidate ≠ 0 → candidate.toNat < d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258)
    (oldLength : d.match_length.toNat ≤ 258) :
    ∃ after pos len, slowFind (some (.tab ds)) candidate h = .ok ((), after) ∧
      DGood after r ds z (matchState d pos len) ∧
      HeapChains after (matchState d pos len) (d.strstart.toNat + 1) ∧ len.toNat ≤ 258 ∧ SearchEvidence d wa pos len ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      (3 ≤ d.lookahead.toNat → d.match_length.toNat ≤ d.lookahead.toNat → len.toNat ≤ d.lookahead.toNat) ∧
      Shape h after ∧ Frame h after (fun b => b = ds) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases active : (candidate != 0 && d.prev_length < d.max_lazy_match &&
      d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) = true
  · have conditions := active
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at conditions
    have nz : candidate ≠ 0 := conditions.1.1
    have nonzero : 1 ≤ candidate.toNat := by
      have ne : candidate.toNat ≠ 0 := by intro eq; exact nz (UInt32.toNat_inj.mp eq)
      omega
    have wsize : 262 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have pow := Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
      change 512 ≤ 2 ^ d.w_bits.toNat at pow
      omega
    have distance := machine_distance (older nz) wsize conditions.2
    obtain ⟨len, ms, best, run, lenEq, lower, upper, matching, _, _⟩ := longest_match_chains_room
      good heapChains win prev head hw hp hq chains hash keyBound published link nonzero (older nz)
      distance range room previous
    have clippedBound : lmResult best d.lookahead.toNat ≤ best := by
      unfold lmResult
      split <;> omega
    have count : len.toNat = lmResult best d.lookahead.toNat := by
      rw [lenEq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have bestBound : len.toNat ≤ best := by rw [count]; exact clippedBound
    have lookBound : len.toNat ≤ d.lookahead.toNat := by rw [count]; unfold lmResult; split <;> omega
    have length : len.toNat ≤ 258 := Nat.le_trans bestBound upper
    have evidence : SearchEvidence d wa ms len := by
      rcases matching with same | improved
      · exact Or.inr (Or.inl (by rw [same.1] at bestBound; exact bestBound))
      · exact Or.inr (Or.inr (Or.inr (improved.2.take bestBound)))
    let dm := matchState d ms len
    let hm := setD h ds dm
    have write : wr (some (.tab ds)) (fun d => { d with match_length := len }) (hAt h ds d ms) =
        .ok ((), hm) := by simp [wrD_eq, hAt, hm, dm, matchState, setD, upd_upd]
    have state : hm.dstates ds = some dm := by simp [hm]
    by_cases reject : rejectShort dm = true
    · let df := matchState d ms 2
      have goodResult := matchState_good good heapChains ms 2
      refine ⟨setD h ds df, ms, 2, ?_, goodResult.1, goodResult.2, by decide, Or.inr (Or.inr (Or.inl (by decide))), rfl, byte_frame_setD h ds df, (fun enough _ => by change 2 ≤ d.lookahead.toNat; omega), state_store_full_storage good.live.hs df⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [ite_eq_left reject]
      simp [wrD_eq, hm, df, dm, matchState, setD_setD, MIN_MATCH_u]
    · have goodResult := matchState_good good heapChains ms len
      refine ⟨hm, ms, len, ?_, goodResult.1, goodResult.2, length, evidence, rfl, byte_frame_setD h ds dm, (fun _ _ => lookBound), state_store_full_storage good.live.hs dm⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [ite_eq_right reject]
      rfl
  · refine ⟨h, d.match_start, d.match_length, ?_, ?_, ?_, oldLength, Or.inl ⟨rfl, rfl⟩, rfl, ByteFrame.refl h _, (fun _ oldBound => oldBound), full_storage_refl h _⟩
    · unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs]
      rw [ite_eq_right active]
      rfl
    · simpa only [matchState] using good
    · simpa only [matchState] using heapChains


/-- Actual hash insertion, lazy-field preparation and conditional matching compose the full private heap frame when three key bytes are present. -/
theorem slow_search_room_full_storage {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (length : d.match_length.toNat ≤ 258)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      DGood after r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len) ∧
      HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧ len.toNat ≤ d.lookahead.toNat ∧
      (3 ≤ len.toNat → d.match_length.toNat < len.toNat →
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨key, keyBound, hash, inserted, goodI, chainsI, older, published, linked⟩ :=
    insert_published_three good env chains ordered range lookahead form
  let di := { d with ins_h := key }
  let hi := insertedHeap h ds p q d pa qa key
  let dm := lazyPrepare di
  let hm := setD hi ds dm
  let prev := pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat)
  let head := qa.set! key.toNat d.strstart.toUInt16
  let candidate := (wfn qa key.toNat).toUInt32
  have goodM : DGood hm r ds z dm := (lazy_prepare_good goodI chainsI).1
  have chainsM : HeapChains hm dm (d.strstart.toNat + 1) := (lazy_prepare_good goodI chainsI).2
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
  obtain ⟨after, pos, len, findRun, goodF, chainsF, lenBound, evidence, bytesF, storageF, clippedF, shapeF, fullF, _liveF, allocF, nextF⟩ := slow_find_room_full_storage goodM chainsM
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
  have extent := window_extent good env.win env.wbytes
  obtain ⟨shapeI, fullI, _liveI, allocI, nextI⟩ :=
    insert_string_run_full_storage good env d.strstart (by omega) (by omega) inserted
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


/-- Every actual initialized search retains the full private object frame,
including the fewer-than-three-byte branch which skips insertion. -/
theorem slow_search_run_full_storage {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {input : Nat → UInt8}
    {candidate : UInt32} (boundary : ContentBoundary h r ds z d input origin base xs)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (run : slowSearch (some (.tab ds)) h = .ok (candidate, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases three : 3 ≤ d.lookahead.toNat
  · obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
    obtain ⟨wv, wbytes, pointerV, bytesV, _view, hashForm⟩ := boundary.data
    have windowV : wv = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using pointerV.symm
    subst wv
    have arrayV : wbytes = wa := Option.some.inj (bytesV.symm.trans env.wbytes)
    subst wbytes
    obtain ⟨key, other, pos, len, tested, _goodA, _chainsA, _bound, _clipped, _matching,
      _bytesA, _formA, _storage, shape, frame, live, alloc, next⟩ :=
      slow_search_room_full_storage boundary.good env chains (Nat.le_refl _) boundary.range three (room three)
        boundary.history.1 (hashForm three)
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    exact ⟨shape, frame, live, alloc, next⟩
  · have tested := (slow_search_fewer_three boundary.good boundary.chains (by omega)).1
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    obtain ⟨shape, frame, live, alloc, next⟩ := state_store_full_storage boundary.good.live.hs (lazyPrepare d)
    exact ⟨shape, full_frame_weaken frame (fun _ same => Or.inr (Or.inl same)), live, alloc, next⟩

/-- Initialized search actually returns its content cutpoint and the full
heap/object/allocation frame on the same heap. No callee contract is assumed. -/
theorem slow_search_initialized_full_storage {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ w wa candidate after result,
      slowSearch (some (.tab ds)) h = .ok (candidate, after) ∧
      SearchBoundary after r ds z result input origin base xs w wa ∧
      SearchWorkFrame d result ∧ StreamBuffers after r ∧ ByteFrame h after (fun k => k = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w, wa, candidate, after, result, run, cut, fields, buffersA, bytes⟩ :=
    slow_search_initialized_boundary boundary frontier buffers room
  exact ⟨w, wa, candidate, after, result, run, cut, fields, buffersA, bytes,
    slow_search_run_full_storage boundary room run⟩

end Zlib.Deflate.Engine.Proofs
