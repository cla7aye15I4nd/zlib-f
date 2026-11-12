import ZlibF.Proof.«deflate.c.engine.slow-search»

/-! # Search near EOF uses physical comparison room and clipped matches -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A shorter prefix of matching window bytes is still a valid match. -/
theorem GoodMatch.take {wa : Array UInt8} {ss ws m len n : Nat}
    (matching : GoodMatch wa ss ws m len) (bound : n ≤ len) : GoodMatch wa ss ws m n :=
  ⟨matching.1, matching.2.1, Nat.le_trans bound matching.2.2.1,
    fun j fit => matching.2.2.2 j (Nat.lt_of_lt_of_le fit bound)⟩

/-- Actual insertion only requires the three real key bytes. The source
array and word-store bounds follow from that valid-data extent. -/
theorem insert_published_three {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
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
      DGood after r ds z d' ∧ HeapChains after d' (d.strstart.toNat + 1) ∧
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
  obtain ⟨key0, after, run0, good0, chain0, _⟩ := insert_string_good_chains good env chains d.strstart
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

/-- Physical comparison room supplies LMEnv independently of the number
of valid lookahead bytes. The matcher itself clips its result to lookahead. -/
theorem match_environment_room {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat))
    (hash : (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key)
    (keyBound : key < d.hash_size.toNat) (published : (wfn qa key).toNat = d.strstart.toNat)
    (link : (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    LMEnv h ds d w p wa pa candidate := by
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  subst w0 p0
  obtain ⟨wa0, getW, sizeW⟩ := blocks.wa
  obtain ⟨pa0, getP, sizeP⟩ := blocks.pa
  have eqW : wa0 = wa := Option.some.inj (getW.symm.trans hw)
  have eqP : pa0 = pa := Option.some.inj (getP.symm.trans hp)
  subst wa0 pa0
  have window : d.strstart.toNat + d.lookahead.toNat ≤ 2 * d.w_size.toNat := by
    simpa only [good.inv.wsz] using range
  have physical : d.strstart.toNat + 262 ≤ 2 * d.w_size.toNat := by
    simpa only [good.inv.wsz] using room
  refine ⟨good.live.hs, win, hw, prev, hp,
    ⟨d.w_bits.toNat, good.inv.wsize, good.inv.wbits_lo, good.inv.wbits_hi⟩, ?_,
    by omega, by omega, by omega, by omega, previous, nonzero, older, distance, ?_⟩
  · apply UInt32.toNat_inj.mp
    rw [good.inv.wmask]
    have positive : 1 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have := Nat.two_pow_pos d.w_bits.toNat
      omega
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using positive)]
    rfl
  · exact chain_ok_of_chains (hash_parameters good.inv) chains hash keyBound published link nonzero older distance

/-- `local uInt longest_match(deflate_state *s, IPos cur_match)`.
The general matcher theorem already handles clipping to short lookahead.
This heap bridge obtains its comparison room from the explicit physical
window bound, rather than assuming at least 262 real input bytes. -/
theorem longest_match_chains_room {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    ∃ (len ms : UInt32) (best : Nat),
      longest_match (some (.tab ds)) candidate h = .ok (len, hAt h ds d ms) ∧
      len = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
        (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) ∧
      DGood (hAt h ds d ms) r ds z { d with match_start := ms } ∧
      HeapChains (hAt h ds d ms) { d with match_start := ms } (d.strstart.toNat + 1) := by
  have env := match_environment_room good win prev head hw hp hq chains hash keyBound published
    link nonzero older distance range room previous
  obtain ⟨len, after, ms, best, run, result, eq, lower, upper, matching⟩ := longest_match_ok env
  subst after
  have inv : DStInv h ds { d with match_start := ms } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have kept := good.setD' (d' := { d with match_start := ms }) rfl good.live.status inv (by trkeep)
  refine ⟨len, ms, best, run, result, lower, upper, matching, kept, ?_⟩
  simpa only [HeapChains, hAt, setD] using heapChains
/-- The real conditional search and short-match filter work with
physical comparison room even when lookahead is below MIN_LOOKAHEAD.
Improving matches retain only the clipped byte prefix returned by C. -/
theorem slow_find_room_storage {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
      (after = h ∨ ∃ e, after = setD h ds e) := by
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
      refine ⟨setD h ds df, ms, 2, ?_, goodResult.1, goodResult.2, by decide, Or.inr (Or.inr (Or.inl (by decide))), rfl, byte_frame_setD h ds df, fun enough _ => by change 2 ≤ d.lookahead.toNat; omega,
        Or.inr ⟨df, rfl⟩⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [if_pos reject]
      simp [wrD_eq, state, hm, df, dm, matchState, setD_setD, MIN_MATCH_u]
    · have goodResult := matchState_good good heapChains ms len
      refine ⟨hm, ms, len, ?_, goodResult.1, goodResult.2, length, evidence, rfl, byte_frame_setD h ds dm, fun _ _ => lookBound,
        Or.inr ⟨dm, rfl⟩⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [if_neg reject]
      rfl
  · refine ⟨h, d.match_start, d.match_length, ?_, ?_, ?_, oldLength, Or.inl ⟨rfl, rfl⟩, rfl, ByteFrame.refl h _, fun _ oldBound => oldBound,
      Or.inl rfl⟩
    · unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs]
      rw [if_neg active]
      rfl
    · simpa only [matchState] using good
    · simpa only [matchState] using heapChains


/-- Actual insertion, lazy-field updates, conditional matching and the
short filter need three valid key bytes plus physical comparison room.
The returned length is bounded by real lookahead, even below 262. -/
theorem slow_search_room_storage {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
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
      ∃ e, after = setD (insertedHeap h ds p q d pa qa key) ds e := by
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
  obtain ⟨after, pos, len, findRun, goodF, chainsF, lenBound, evidence, bytesF, storageF, clippedF, heapF⟩ := slow_find_room_storage goodM chainsM
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
  refine ⟨key, after, pos, len, slow_search_composes good.live.hs ready inserted findRun,
    goodF, chainsF, lenBound, clippedF lookahead (by change 2 ≤ d.lookahead.toNat; omega),
    ?_, frame, nextForm, stored, ?_⟩
  rotate_left
  · rcases heapF with same | ⟨e, eq⟩
    · exact ⟨dm, same⟩
    · exact ⟨e, by rw [eq]; exact setD_setD _ _ _ _⟩
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


/-- With fewer than three key bytes the actual search skips insertion
and longest_match. It still performs the real lazy-field preparation and
returns NIL. Stale hash contents do not become a candidate. -/
theorem slow_search_fewer_three {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (short : d.lookahead.toNat < 3) :
    slowSearch (some (.tab ds)) h = .ok (0, setD h ds (lazyPrepare d)) ∧
      DGood (setD h ds (lazyPrepare d)) r ds z (lazyPrepare d) ∧
      HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top ∧
      ByteFrame h (setD h ds (lazyPrepare d)) (fun i => i = ds) := by
  have prepared := lazy_prepare_good good chains
  have skip : ¬ d.lookahead ≥ MIN_MATCH_u := by
    change ¬ MIN_MATCH_u ≤ d.lookahead
    rw [UInt32.le_iff_toNat_le]
    change ¬ 3 ≤ d.lookahead.toNat
    omega
  have write : wr (some (.tab ds)) lazyPrepare h = .ok ((), setD h ds (lazyPrepare d)) := by
    simp only [wrD_eq, good.live.hs]
  have find : slowFind (some (.tab ds)) 0 (setD h ds (lazyPrepare d)) =
      .ok ((), setD h ds (lazyPrepare d)) := by
    unfold slowFind
    simp only [bind_app, ldDeflateState_tab prepared.1.live.hs,
      show ((0 : UInt32) != 0) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false, pure_app]
  refine ⟨?_, prepared.1, prepared.2, byte_frame_setD h ds (lazyPrepare d)⟩
  unfold slowSearch
  simp only [bind_app, rdD_eq, good.live.hs, skip, ite_false, pure_app, initial_match_length]
  change (do
    wr (some (.tab ds)) lazyPrepare
    slowFind (some (.tab ds)) 0
    pure (0 : UInt32)) h = _
  simp only [bind_app, write, find, pure_app]

end Zlib.Deflate.Engine.Proofs
