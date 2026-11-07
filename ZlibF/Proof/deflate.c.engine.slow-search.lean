import ZlibF.Proof.«deflate.c.engine.slow-find»

/-! # The actual slow strategy's insertion and match-search prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def lazyPrepare (d : DeflateState) : DeflateState :=
  { d with prev_length := d.match_length, prev_match := d.match_start, match_length := 2 }

theorem initial_match_length : (MIN_MATCH_u - 1 : UInt32) = 2 := by decide

theorem lazy_prepare_inv {h : Heap} {ds : Nat} {d : DeflateState} (inv : DStInv h ds d) :
    DStInv h ds (lazyPrepare d) := by
  exact { inv with blocks := inv.blocks_keys (d' := lazyPrepare d) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }

theorem lazy_prepare_chains {h : Heap} {ds top : Nat} {d : DeflateState} (chains : HeapChains h d top) :
    HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

theorem lazy_prepare_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) :
    DGood (setD h ds (lazyPrepare d)) r ds z (lazyPrepare d) ∧
      HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top := by
  exact ⟨good.setD' (d' := lazyPrepare d) rfl good.live.status (lazy_prepare_inv good.inv) (by trkeep),
    lazy_prepare_chains chains⟩

theorem slow_search_composes {h after : Heap} {ds p q : Nat} {d : DeflateState}
    {pa qa : Array UInt16} {key : UInt32}
    (state : h.dstates ds = some d) (ready : d.lookahead ≥ MIN_MATCH_u)
    (inserted : INSERT_STRING (some (.tab ds)) d.strstart h =
      .ok ((wfn qa key.toNat).toUInt32, insertedHeap h ds p q d pa qa key))
    (findRun : slowFind (some (.tab ds)) (wfn qa key.toNat).toUInt32
      (setD (insertedHeap h ds p q d pa qa key) ds (lazyPrepare { d with ins_h := key })) = .ok ((), after)) :
    slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) := by
  let hi := insertedHeap h ds p q d pa qa key
  let hm := setD hi ds (lazyPrepare { d with ins_h := key })
  have write : wr (some (.tab ds)) lazyPrepare hi = .ok ((), hm) := by
    simp [wrD_eq, hi, insertedHeap, hm]
  unfold slowSearch
  simp only [bind_app, rdD_eq, state, ready, if_true, inserted, initial_match_length]
  change (do
    wr (some (.tab ds)) lazyPrepare
    slowFind (some (.tab ds)) (wfn qa key.toNat).toUInt32
    pure (wfn qa key.toNat).toUInt32) hi = _
  rw [bind_app, write]
  simp only []
  rw [bind_app, findRun]
  rfl

/-- `slowSearch` is the source prefix named by slow_body_source.
Actual insertion establishes the matcher environment. The lazy-match
field write and all guarded searches and short-match filters execute in
source order. The result retains DGood, H and the finite length bound.
No callee execution contract is a premise.
-/
theorem slow_search_boundary {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      DGood after r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len) ∧
      HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → d.match_length.toNat < len.toNat →
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key := by
  obtain ⟨key, keyBound, hash, inserted, goodI, chainsI, older, published, linked⟩ :=
    insert_published_chain good env chains ordered range lookahead form
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
  obtain ⟨after, pos, len, findRun, goodF, chainsF, lenBound, evidence, bytesF⟩ := slow_find_boundary goodM chainsM
    (by simpa only [dm, di, lazyPrepare] using env.win)
    (by simpa only [dm, di, lazyPrepare] using env.prevp)
    (by simpa only [dm, di, lazyPrepare] using env.headp)
    getW getP getQ actualChains originalHash keyBound published linked
    (by intro nz; apply older; simpa only [candidate, UInt16.toNat_toUInt32] using
      (show candidate.toNat ≠ 0 from fun eq => nz (UInt32.toNat_inj.mp eq)))
    range lookahead length (by change (2 : UInt32).toNat ≤ 258; decide)
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
  refine ⟨key, after, pos, len, slow_search_composes good.live.hs ready inserted findRun,
    goodF, chainsF, lenBound, ?_, frame, nextForm⟩
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

theorem slow_search_matched {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      DGood after r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len) ∧
      HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → d.match_length.toNat < len.toNat →
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) := by
  obtain ⟨key, after, pos, len, run, goodA, chainsA, lengthA, quality, _, _⟩ :=
    slow_search_boundary good env chains ordered range lookahead length form
  exact ⟨key, after, pos, len, run, goodA, chainsA, lengthA, quality⟩

theorem slow_search_preserves {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key after pos len,
      slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) ∧
      DGood after r ds z (matchState (lazyPrepare { d with ins_h := key }) pos len) ∧
      HeapChains after (matchState (lazyPrepare { d with ins_h := key }) pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 := by
  obtain ⟨key, after, pos, len, run, goodA, chainsA, lengthA, _⟩ :=
    slow_search_matched good env chains ordered range lookahead length form
  exact ⟨key, after, pos, len, run, goodA, chainsA, lengthA⟩

end Zlib.Deflate.Engine.Proofs
