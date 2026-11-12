import ZlibF.Proof.«deflate.c.universal-window»

/-!
# deflate.c, engine: hash chains read through a table view

At level 0, `deflate_stored` slides the window without the hash tables and counts the slides in
`matches`. With one pending slide the invariant describes the tables as they will be after
`slide_hash` (`SlidChains`, every entry read through `slideVal`); with two it describes nothing.
`deflateSetDictionary` runs `fill_window` and its insertion loop on such tables.

`ViewChains v` is the chain invariant `HashChains` of the tables read through the view `v`: as they
are (`exact`), slid once (`slid`), or no fact (`none`). It obeys the same laws as `HashChains`:
insertion at the frontier (`view_insert`), the slide of `fill_window` (`view_slide`), frames and
monotonicity, and empty heads. The slid law needs no fact on the inserted position: an inserted
position `str` appears in the slid view as `str - w_size` or `NIL`, which is out of the window
distance of every later frontier, so the walk never follows it. The engine lemmas of the pending
insertion below are those of `deflate.c.engine.fill-insert-full-storage` with `HeapChains` replaced
by `VHeapChains v`, the same proofs with the laws of the view.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-! ## The view and its laws -/

/-- How the chain invariant reads the tables: as they are, through one pending slide, or not at
all. -/
inductive TabView where
  | exact
  | slid
  | none

/-- The chain invariant of the tables `head` and `prev` read through the view `v`. -/
def ViewChains : TabView → (Nat → UInt16) → (Nat → UInt16) → (Nat → UInt8) → UInt32 → UInt32 → UInt32 →
    UInt32 → Nat → Nat → Prop
  | .exact, head, prev, w, n, hsh, hm, ws, top, lim => HashChains head prev w n hsh hm ws.toNat top lim
  | .slid, head, prev, w, n, hsh, hm, ws, top, lim =>
      HashChains (fun i => slideVal ws (head i)) (fun i => slideVal ws (prev i)) w n hsh hm ws.toNat top lim
  | .none, _, _, _, _, _, _, _, _, _ => True

theorem slideVal_zero (ws : UInt32) (hw : ws.toNat ≤ 65536) : slideVal ws 0 = 0 := by
  apply UInt16.toNat_inj.mp
  rw [slideVal_toNat ws 0 hw]
  split <;> simp

theorem view_congr {v : TabView} {h1 p1 h2 p2 : Nat → UInt16} {w w' : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim : Nat} (hc : ViewChains v h1 p1 w n hsh hm ws top lim)
    (hH : ∀ i, h2 i = h1 i) (hP : ∀ i, p2 i = p1 i)
    (hw : ∀ i, i < lim → w' i = w i) : ViewChains v h2 p2 w' n hsh hm ws top lim := by
  cases v with
  | exact => exact chains_congr hc hH hP hw
  | slid => exact chains_congr hc (fun i => by simp only [hH]) (fun i => by simp only [hP]) hw
  | none => trivial

theorem view_mono {v : TabView} {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim top' lim' : Nat} (hc : ViewChains v h1 p1 w n hsh hm ws top lim)
    (ht : top ≤ top') (hl : lim ≤ lim') : ViewChains v h1 p1 w n hsh hm ws top' lim' := by
  cases v with
  | exact => exact chains_mono hc ht hl
  | slid => exact chains_mono hc ht hl
  | none => trivial

/-- Empty heads establish every view. -/
theorem view_empty {v : TabView} {head prev : Nat → UInt16} {w : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim : Nat} (hw : ws.toNat ≤ 65536) (heads : ∀ k, k < n.toNat → head k = 0) :
    ViewChains v head prev w n hsh hm ws top lim := by
  cases v with
  | exact => exact chains_empty heads
  | slid => exact chains_empty (fun k hk => by simp only [heads k hk, slideVal_zero ws hw])
  | none => trivial

/-- **One insertion keeps the slid view.** The inserted position `str` appears in the view as
`str - w_size` or `NIL`: never followed, and never constrained at the new frontier `str + 1`. The
slot it overwrites is not the slot of any constrained node, which lies less than `w_size` below
`str`. -/
theorem chains_insert_slid {h1 p1 h2 p2 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim b : Nat}
    (hc : HashChains (fun i => slideVal ws (h1 i)) (fun i => slideVal ws (p1 i)) w n hsh hm ws.toNat top lim)
    (hb2 : ws.toNat = 2 ^ b) (hw16 : ws.toNat ≤ 65536)
    {str x : Nat} {s16 : UInt16} (htop : top ≤ str) (hs16 : s16.toNat = str)
    (hH : ∀ i, h2 i = if i = x then s16 else h1 i)
    (hP : ∀ i, p2 i = if i = str &&& (ws.toNat - 1) then h1 x else p1 i) :
    HashChains (fun i => slideVal ws (h2 i)) (fun i => slideVal ws (p2 i)) w n hsh hm ws.toNat (str + 1) lim := by
  have hws : 0 < ws.toNat := by rw [hb2]; exact Nat.two_pow_pos b
  have sv := slideVal_toNat ws s16 hw16
  rw [hs16] at sv
  have A : ∀ k p, k < n.toNat →
      Reach (fun i => slideVal ws (h2 i)) (fun i => slideVal ws (p2 i)) ws.toNat (str + 1) k p →
      (p = (slideVal ws s16).toNat) ∨ Reach (fun i => slideVal ws (h1 i)) (fun i => slideVal ws (p1 i)) ws.toNat top k p := by
    intro k p hk hr
    induction hr with
    | head =>
      simp only [hH]
      split
      · exact Or.inl rfl
      · exact Or.inr Reach.head
    | @step p _ hp ht ih =>
      rcases ih with e | hr
      · exfalso
        rw [e] at hp ht
        split at sv <;> omega
      · have hpt := (hc.node k p hk hr hp (by omega)).1
        have slot : (p &&& (ws.toNat - 1) = str &&& (ws.toNat - 1)) = False :=
          eq_false (and_wm_ne hb2 (by omega) (by omega))
        have := Reach.step hr hp (by omega)
        simp only [hP, slot, ite_false] at this ⊢
        exact Or.inr this
  refine ⟨fun k p hk hr hp ht => ?_⟩
  rcases A k p hk hr with e | hr0
  · exfalso
    rw [e] at hp ht
    split at sv <;> omega
  · obtain ⟨a1, a2, a3, a4⟩ := hc.node k p hk hr0 hp (by omega)
    have slot : (p &&& (ws.toNat - 1) = str &&& (ws.toNat - 1)) = False :=
      eq_false (and_wm_ne hb2 (by omega) (by omega))
    refine ⟨by omega, a2, a3, ?_⟩
    simp only [hP, slot, ite_false]
    exact a4

/-- **One insertion keeps every view** (`INSERT_STRING` at the frontier). -/
theorem view_insert {v : TabView} {h1 p1 h2 p2 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim b : Nat} (hc : ViewChains v h1 p1 w n hsh hm ws top lim)
    (hb2 : ws.toNat = 2 ^ b) (hw16 : ws.toNat ≤ 65536)
    {str x : Nat} {s16 : UInt16} (htop : top ≤ str) (hlim : str + 3 ≤ lim)
    (hx : (hkey hsh hm w str).toNat = x) (hxn : x < n.toNat) (hs16 : s16.toNat = str)
    (hH : ∀ i, h2 i = if i = x then s16 else h1 i)
    (hP : ∀ i, p2 i = if i = str &&& (ws.toNat - 1) then h1 x else p1 i) :
    ViewChains v h2 p2 w n hsh hm ws (str + 1) lim := by
  cases v with
  | exact => exact chains_insert hc hb2 htop hlim hx hxn hs16 hH hP
  | slid => exact chains_insert_slid hc hb2 hw16 htop hs16 hH hP
  | none => trivial

/-- **`slide_hash` keeps every view** (with the window copy of `fill_window`). -/
theorem view_slide {v : TabView} {h1 p1 h2 p2 : Nat → UInt16} {w w' : Nat → UInt8} {n hsh hm ws : UInt32}
    {top lim b : Nat} (hc : ViewChains v h1 p1 w n hsh hm ws top lim)
    (hb2 : ws.toNat = 2 ^ b) (hw16 : ws.toNat ≤ 65536)
    (hH : ∀ i, i < n.toNat → h2 i = slideVal ws (h1 i))
    (hP : ∀ i, i < ws.toNat → p2 i = slideVal ws (p1 i))
    (hw : ∀ i, i + ws.toNat < lim → w' i = w (i + ws.toNat)) :
    ViewChains v h2 p2 w' n hsh hm ws (top - ws.toNat) (lim - ws.toNat) := by
  cases v with
  | exact => exact chains_slide hc hb2 hw16 hH hP hw
  | slid =>
    exact chains_slide (h2 := fun i => slideVal ws (h2 i)) (p2 := fun i => slideVal ws (p2 i)) hc hb2 hw16
      (fun i hi => by simp only [hH i hi]) (fun i hi => by simp only [hP i hi]) hw
  | none => trivial

/-! ## The view on the heap -/

/-- `HeapChains` through the view `v`. `VHeapChains .exact` is `HeapChains`; `VHeapChains .slid` at
`strstart - insert` is `SlidChains`. -/
def VHeapChains (v : TabView) (h : Heap) (d : DeflateState) (top : Nat) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    ViewChains v (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask d.w_size top
      (d.strstart.toNat + d.lookahead.toNat)

theorem vheap_up {v : TabView} {h : Heap} {d : DeflateState} {top next : Nat}
    (chains : VHeapChains v h d top) (ordered : top ≤ next) : VHeapChains v h d next := by
  obtain ⟨w, p, q, wa, pa, qa, hw, hp, hq, a, b, c, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, hw, hp, hq, a, b, c, view_mono H ordered (Nat.le_refl _)⟩

/-- The memory premises for insertion, from the representation and the view chains. -/
theorem vheap_environment {v : TabView} {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : VHeapChains v h d top) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa ∧
      ViewChains v (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
        d.w_size top (d.strstart.toNat + d.lookahead.toNat) := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by
    simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  have qe : q0 = q := by
    simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  subst w0 p0 q0
  have hsize : d.hash_size.toNat ≤ qa.size := by
    obtain ⟨qa0, get, size⟩ := blocks.qa
    have eq : qa0 = qa := Option.some.inj (get.symm.trans hq)
    subst qa0
    omega
  have psize : d.w_size.toNat ≤ pa.size := by
    obtain ⟨pa0, get, size⟩ := blocks.pa
    have eq : pa0 = pa := Option.some.inj (get.symm.trans hp)
    subst pa0
    omega
  have mask : d.w_mask.toNat < d.w_size.toNat := by
    have pos : 0 < d.w_size.toNat := by rw [good.inv.wsize]; exact Nat.two_pow_pos _
    rw [good.inv.wmask]
    omega
  exact ⟨w, p, q, wa, pa, qa, ⟨win, hw, blocks.wro, head, hq, prev, hp,
    blocks.pq.symm, hsize, psize, mask, hash_parameters good.inv⟩, H⟩

/-- Writes beyond the valid data keep the view chains. -/
theorem vheap_window_write {v : TabView} {h : Heap} {d : DeflateState} {top w : Nat}
    {wa wa' : Array UInt8} (chains : VHeapChains v h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (keepBytes : ∀ i, i < d.strstart.toNat + d.lookahead.toNat → bfn wa' i = bfn wa i) :
    VHeapChains v { h with bytes := upd h.bytes w (some wa') } d top := by
  obtain ⟨w0, p, q, a, pa, qa, win0, prev, head, get0, hp, hq, H⟩ := chains
  have id : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  subst w0
  have eq : a = wa := Option.some.inj (get0.symm.trans get)
  subst a
  exact ⟨w, p, q, wa', pa, qa, win, prev, head, by simp, hp, hq,
    view_congr H (fun _ => rfl) (fun _ => rfl) keepBytes⟩

/-- A state write that keeps the window, the tables, the sizes and the data end keeps the view
chains. -/
theorem vheap_state {v : TabView} {h h' : Heap} {d d' : DeflateState} {top : Nat}
    (chains : VHeapChains v h d top) (bytes : h'.bytes = h.bytes) (words : h'.words = h.words)
    (win : d'.window = d.window) (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (sizes : d'.hash_size = d.hash_size ∧ d'.hash_shift = d.hash_shift ∧ d'.hash_mask = d.hash_mask ∧
      d'.w_size = d.w_size)
    (lim : d'.strstart.toNat + d'.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat) :
    VHeapChains v h' d' top := by
  obtain ⟨w, p, q, wa, pa, qa, hw, hp, hq, a, b, c, H⟩ := chains
  obtain ⟨s1, s2, s3, s4⟩ := sizes
  refine ⟨w, p, q, wa, pa, qa, by rw [win]; exact hw, by rw [prev]; exact hp, by rw [head]; exact hq,
    by rw [bytes]; exact a, by rw [words]; exact b, by rw [words]; exact c, ?_⟩
  rw [s1, s2, s3, s4, lim]
  exact H

/-! ## Insertion -/

/-- `INSERT_STRING` keeps the representation and the view chains. -/
theorem insert_string_good_vchains {v : TabView} {h : Heap} {r : ZStreamRef} {sr wb hb pb top bits : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : DGood h r sr z d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : ViewChains v (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size top (d.strstart.toNat + d.lookahead.toNat))
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (window : d.strstart.toNat + d.lookahead.toNat ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after, INSERT_STRING (some (.tab sr)) str h =
        .ok ((wfn ha key.toNat).toUInt32, after) ∧
      DGood after r sr z { d with ins_h := key } ∧
      VHeapChains v after { d with ins_h := key } (str.toNat + 1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  have fit : str.toNat + 2 < wa.size := by omega
  have ws16 : d.w_size.toNat ≤ 65536 := by have := (slide_window_sizes good).2; omega
  obtain ⟨key, keyEq, keyBound, run⟩ := INSERT_STRING_ok good.live.hs env str fit (by omega)
  have byte : wa[str.toNat + 2]! = bfn wa (str.toNat + 2) := by
    simp [bfn, Array.getD_eq_getD_getElem?, fit]
  have hash : key = hkey d.hash_shift d.hash_mask (bfn wa) str.toNat := by
    rw [keyEq, byte]
    exact hkey_of_form env.params form
  have s16 : str.toUInt16.toNat = str.toNat := by
    rw [UInt32.toNat_toUInt16, Nat.mod_eq_of_lt position]
  have slot : (str &&& d.w_mask).toNat < pa.size := by
    rw [UInt32.toNat_and]
    have bound := Nat.and_le_right (n := str.toNat) (m := d.w_mask.toNat)
    have size := env.wsize
    have small := env.wmask
    omega
  have headFit : key.toNat < ha.size := by have size := env.hsize; omega
  have H := view_insert chains ws ws16 ordered data
    (show (hkey d.hash_shift d.hash_mask (bfn wa) str.toNat).toNat = key.toNat by rw [hash])
    keyBound s16
    (fun i => wfn_set ha key.toNat str.toUInt16 headFit i)
    (fun i => by
      simpa only [UInt32.toNat_and, mask] using
        wfn_set pa (str &&& d.w_mask).toNat (wfn ha key.toNat) slot i)
  let pa' := pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)
  let ha' := ha.set! key.toNat str.toUInt16
  have prevGood := good.words_set pb pa' pa env.pwords (by simp [pa'])
  have headGood := prevGood.words_set hb ha' ha
    (by simpa [env.hne] using env.hwords) (by simp [ha'])
  have inv : DStInv _ sr { d with ins_h := key } :=
    { headGood.inv with blocks := headGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have updated := headGood.setD' (d' := { d with ins_h := key }) rfl good.live.status inv (by trkeep)
  refine ⟨key, _, run, updated, ?_, ?_⟩
  · refine ⟨wb, pb, hb, wa, pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat),
      ha.set! key.toNat str.toUInt16, env.win, env.prevp, env.headp, ?_, ?_, ?_, ?_⟩
    · exact env.wbytes
    · simp [pa', upd_ne _ _ _ _ env.hne.symm]
    · simp [ha']
    · simpa only [UInt32.toNat_and, mask] using H
  · rw [keyEq, byte]
    exact form_next form

/-- One deferred insertion of `fill_window`, with its complete heap frame, through the view. -/
theorem fill_insert_step_full_storage_v {v : TabView} {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32) (brk : Bool)
    (good : DGood h r ds z d) (chains : VHeapChains v h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (positive : 1 ≤ d.insert.toNat) (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after,
      let result := pendingInsertState d key
      fillInsertBody (some (.tab ds)) (str, brk) h =
        .ok ((str + 1, result.lookahead + result.insert < MIN_MATCH_u), after) ∧
      DGood after r ds z result ∧ VHeapChains v after result (str.toNat + 1) ∧ after.bytes = h.bytes ∧
      (str + 1).toNat = str.toNat + 1 ∧ result.insert.toNat = d.insert.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (str.toNat + 1) result.ins_h ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w0, p, q, bytes, pa, qa, env, H⟩ := vheap_environment good chains
  have windowId : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have arrayId : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst bytes
  have extent := window_extent good win get
  have data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat := by omega
  obtain ⟨key, hi, insertRun, goodI, chainsI, formI⟩ := insert_string_good_vchains good env H str
    good.inv.wsize good.inv.wmask (Nat.le_refl _) data (by omega) (by omega) form
  obtain ⟨other, _, _, exactRun⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
  have pair := Except.ok.inj (insertRun.symm.trans exactRun)
  have byteFrame : hi.bytes = h.bytes := congrArg (fun x => x.2.bytes) pair
  have stored : ByteFrame h hi (fun i => i = ds) := by
    have heapEq := congrArg Prod.snd pair
    change hi = _ at heapEq
    rw [heapEq]
    exact ⟨rfl, fun _ _ => rfl,
      fun i outside => by simp [upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
  obtain ⟨shapeI, frameI, _liveI, allocI, nextI⟩ :=
    insert_string_run_full_storage good env str (by omega) (by omega) insertRun
  let result := pendingInsertState d key
  let after := setD hi ds result
  have inv : DStInv hi ds result :=
    { goodI.inv with blocks := goodI.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA : DGood after r ds z result := goodI.setD' rfl goodI.live.status inv (by trkeep)
  have chainsA : VHeapChains v after result (str.toNat + 1) := by
    obtain ⟨wb, pb, qb, a, pa0, qa0, hw, hp, hq, ha, hpa, hqa, hs⟩ := chainsI
    exact ⟨wb, pb, qb, a, pa0, qa0, hw, hp, hq, ha, hpa, hqa, hs⟩
  have next : (str + 1).toNat = str.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have count : result.insert.toNat = d.insert.toNat - 1 := u32_sub_one positive
  have write : wr (some (.tab ds)) (fun state => { state with insert := state.insert - 1 }) hi =
      .ok ((), after) := by
    simp [wrD_eq, goodI.live.hs, after, result, pendingInsertState]
  have shapeD := shape_setD goodI.live.hs result
  have shapeA := shapeI.trans shapeD
  have frameD : Frame hi after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame hi ds result) (fun _ same => Or.inr (Or.inl same))
  have frameA := full_frame_trans_shape frameI frameD shapeI
  refine ⟨key, after, ?_, goodA, chainsA, byteFrame, next, count, formI,
    stored.trans (byte_frame_setD hi ds result), shapeA, frameA, full_shape_live_change shapeA, allocI, nextI⟩
  unfold fillInsertBody
  simp only [bind_app, insertRun, write, ldDeflateState_tab goodA.live.hs, pure_app]
  rfl

set_option maxHeartbeats 2000000 in
/-- The complete pending-insertion loop of `fill_window` through the view. -/
theorem fill_insert_loop_full_storage_v {v : TabView} {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32)
    (good : DGood h r ds z d) (chains : VHeapChains v h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ final after result,
      cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false) h =
        .ok (final, after) ∧
      DGood after r ds z result ∧ VHeapChains v after result final.1.toNat ∧ after.bytes = h.bytes ∧
      PendingInsertFrame d result ∧ final.1.toNat + result.insert.toNat = d.strstart.toNat ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) final.1.toNat result.ins_h ∧ ByteFrame h after (fun i => i = ds) ∧ Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let Inv : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ VHeapChains v heap state pos.1.toNat ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    state.strstart.toNat + state.lookahead.toNat ≤ state.window_size.toNat ∧
    pos.1.toNat + state.insert.toNat = state.strstart.toNat ∧
    state.insert.toNat ≤ d.insert.toNat ∧ 2 ≤ state.lookahead.toNat + state.insert.toNat ∧
    pos.2 = decide (state.lookahead.toNat + state.insert.toNat < 3) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧
    PendingInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let Q : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ VHeapChains v heap state pos.1.toNat ∧ heap.bytes = h.bytes ∧
    PendingInsertFrame d state ∧ pos.1.toNat + state.insert.toNat = d.strstart.toNat ∧
    state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧ ByteFrame h heap (fun i => i = ds) ∧ Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧ heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  let rank : (UInt32 × Bool) → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.insert.toNat)).getD 0
  have step : ∀ pos heap, Inv pos heap → ∃ c pos1 heap1,
      fillInsertCond (some (.tab ds)) pos heap = .ok ((c, pos1), heap1) ∧
      (c = false → Q pos1 heap1) ∧
      (c = true → ∃ pos2 heap2, fillInsertBody (some (.tab ds)) pos1 heap1 = .ok (pos2, heap2) ∧
        Inv pos2 heap2 ∧ rank pos2 heap2 < rank pos heap) := by
    intro pos heap inv
    obtain ⟨state, goodS, chainsS, winS, getS, rangeS, cursorS, boundS, lowerS, stopS, formS, frameS, bytesS, storageS, shapeS, fullS, allocS, nextS⟩ := inv
    have startS : state.strstart = d.strstart := congrArg (·.strstart) frameS
    have lookS : state.lookahead = d.lookahead := congrArg (·.lookahead) frameS
    refine ⟨state.insert != 0 && !pos.2, pos, heap, ?_, ?_, ?_⟩
    · simp only [fillInsertCond, bind_app, rdD_eq, goodS.live.hs, pure_app]
    · intro stopped
      have exit : state.insert.toNat = 0 ∨ state.lookahead.toNat + state.insert.toNat < 3 := by
        by_cases zero : state.insert = 0
        · left; rw [zero]; rfl
        · right
          have flag : pos.2 = true := by
            simpa [bne_iff_ne, zero] using stopped
          rw [stopS] at flag
          exact of_decide_eq_true flag
      have count : state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) := by
        rw [lookS] at lowerS exit
        rcases exit with zero | small <;> omega
      exact ⟨state, goodS, chainsS, bytesS, frameS, by rw [startS] at cursorS; exact cursorS, count, formS, storageS, shapeS, fullS, allocS, nextS⟩
    · intro continued
      have guard := continued
      simp only [Bool.and_eq_true, bne_iff_ne] at guard
      have positive : 1 ≤ state.insert.toNat := by
        have ne : state.insert.toNat ≠ 0 := by intro eq; exact guard.1 (UInt32.toNat_inj.mp eq)
        omega
      have readyS : 3 ≤ state.lookahead.toNat + state.insert.toNat := by
        have falseFlag : pos.2 = false := by
          cases bit : pos.2
          · rfl
          · have impossible : False := by simpa [bit] using guard.2
            cases impossible
        have flag : decide (state.lookahead.toNat + state.insert.toNat < 3) = false :=
          stopS.symm.trans falseFlag
        have notLow := of_decide_eq_false flag
        omega
      obtain ⟨key, after, bodyRun, goodA, chainsA, bytesA, next, countA, formA, storageA, shapeA, fullA, _liveA, allocA, nextA⟩ :=
        fill_insert_step_full_storage_v pos.1 pos.2 goodS chainsS winS getS rangeS cursorS positive readyS formS
      let result := pendingInsertState state key
      let stopped : Bool := decide (result.lookahead + result.insert < MIN_MATCH_u)
      let nextPos := (pos.1 + 1, stopped)
      have cursorA : nextPos.1.toNat + result.insert.toNat = result.strstart.toNat := by
        change (pos.1 + 1).toNat + result.insert.toNat = state.strstart.toNat
        rw [next, countA]
        omega
      have rangeA : result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat := rangeS
      have getA : after.bytes w = some wa := by rw [bytesA]; exact getS
      have sum := pending_sum_nat goodA winS getA rangeA (by omega : result.insert.toNat ≤ result.strstart.toNat)
      change (result.lookahead + result.insert).toNat = result.lookahead.toNat + result.insert.toNat at sum
      have stopA : nextPos.2 = decide (result.lookahead.toNat + result.insert.toNat < 3) := by
        change decide (result.lookahead + result.insert < MIN_MATCH_u) = _
        simp only [UInt32.lt_iff_toNat_lt, sum, show MIN_MATCH_u.toNat = 3 from rfl]
      have ownedS : DeflateOwned ds state = DeflateOwned ds d := by
        rw [show state = {d with ins_h := state.ins_h, insert := state.insert} from frameS]
        rfl
      have fullA' : Frame heap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        rw [← ownedS]
        exact fullA
      have fullNext := full_frame_trans_shape fullS fullA' shapeS
      refine ⟨nextPos, after, bodyRun, ⟨result, goodA, ?_, winS, getA, rangeA, cursorA, ?_, ?_, stopA,
        ?_, pending_insert_frame_step frameS key, bytesA.trans bytesS, storageS.trans storageA, shapeS.trans shapeA, fullNext, allocA.trans allocS, nextA.trans nextS⟩, ?_⟩
      · change VHeapChains v after result (pos.1 + 1).toNat
        rw [next]
        exact chainsA
      · rw [countA]
        omega
      · change 2 ≤ state.lookahead.toNat + result.insert.toNat
        rw [countA]
        omega
      · change InsHForm result.hash_shift result.hash_mask (bfn wa) (pos.1 + 1).toNat result.ins_h
        rw [next]
        exact formA
      · simp only [rank, goodS.live.hs, goodA.live.hs, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv (str, false) h :=
    ⟨d, good, chains, win, get, range, cursor, Nat.le_refl _, by omega,
      by simp [show ¬ d.lookahead.toNat + d.insert.toNat < 3 by omega], form, rfl, rfl, ByteFrame.refl h _, Shape.refl h,
      ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩
  have extent := window_extent good win get
  have bound : rank (str, false) h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.insert.toNat < 18446744073709551616
    omega
  obtain ⟨final, after, run, result, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩ :=
    while_heap_rank Inv rank Q step initial bound
  exact ⟨final, after, result, run, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩

set_option maxHeartbeats 2500000 in
/-- Hash seeding and the complete pending insertion through the view. -/
theorem fill_prime_pending_full_storage_v {v : TabView} {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : VHeapChains v h d (d.strstart.toNat - d.insert.toNat))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (pending : d.insert.toNat ≤ d.strstart.toNat) :
    ∃ after result,
      fillPrime (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z result ∧
      VHeapChains v after result (result.strstart.toNat - result.insert.toNat) ∧
      after.bytes = h.bytes ∧ PendingInsertFrame d result ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      (3 ≤ result.lookahead.toNat → result.insert = 0 ∧
        InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h) ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have extent := window_extent good win get
  have sum := pending_sum_nat good win get range pending
  let str := d.strstart - d.insert
  have position : str.toNat = d.strstart.toNat - d.insert.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr pending)
  have cursor : str.toNat + d.insert.toNat = d.strstart.toNat := by omega
  by_cases enter : d.lookahead + d.insert ≥ MIN_MATCH_u
  · have ready : 3 ≤ d.lookahead.toNat + d.insert.toNat := by
      have guard := UInt32.le_iff_toNat_le.mp enter
      rw [sum] at guard
      exact guard
    have fit : str.toNat + 2 ≤ wa.size := by omega
    let seeded := insertSeedState d wa str
    let hs := setD h ds seeded
    have params : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters good.inv
    have inv : DStInv h ds seeded :=
      { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
    have goodS : DGood hs r ds z seeded := good.setD' rfl good.live.status inv (by trkeep)
    have chainsS : VHeapChains v hs seeded str.toNat := by
      obtain ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩ := chains
      rw [← position] at H
      exact ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩
    have formS : InsHForm seeded.hash_shift seeded.hash_mask (bfn wa) str.toNat seeded.ins_h :=
      insert_seed_form (d := d) params fit
    have seedRun : fillInsertSeed (some (.tab ds)) d.window str h = .ok ((), hs) :=
      fill_insert_seed_run good.live.hs win get str fit (by omega) (by
        rw [UInt32.lt_iff_toNat_lt]
        exact (hash_parameters good.inv).hsh_lt)
    obtain ⟨final, after, result, loop, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA, shapeA, fullA, allocA, nextA⟩ :=
      fill_insert_loop_full_storage_v str goodS chainsS win get range cursor ready formS
    have frame : PendingInsertFrame d result := by
      unfold PendingInsertFrame at frameA ⊢
      rw [frameA]
      rfl
    have startA : result.strstart = d.strstart := congrArg (·.strstart) frame
    have lookA : result.lookahead = d.lookahead := congrArg (·.lookahead) frame
    have frontier : final.1.toNat = result.strstart.toNat - result.insert.toNat := by
      change final.1.toNat + result.insert.toNat = d.strstart.toNat at cursorA
      rw [startA]
      omega
    have owned : DeflateOwned ds seeded = DeflateOwned ds d := rfl
    have seedShape := shape_setD good.live.hs seeded
    have seedFrame : Frame h hs (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
      full_frame_weaken (state_store_full_frame h ds seeded) (fun _ same => Or.inr (Or.inl same))
    have loopFrame : Frame hs after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
      rw [← owned]
      exact fullA
    have full := full_frame_trans_shape seedFrame loopFrame seedShape
    refine ⟨after, result, ?_, goodA, ?_, bytesA, frame, countA, ?_,
      (byte_frame_setD h ds seeded).trans storageA, seedShape.trans shapeA, full, allocA, nextA⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, ite_true]
      change (do
        fillInsertSeed (some (.tab ds)) d.window str
        let (_, _) ← cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false)
        pure ()) h = _
      simp only [bind_app, seedRun, loop, pure_app]
    · rw [← frontier]
      exact chainsA
    · intro large
      have zeroNat : result.insert.toNat = 0 := by
        change result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) at countA
        rw [lookA] at large
        omega
      have zero : result.insert = 0 := UInt32.toNat_inj.mp zeroNat
      refine ⟨zero, ?_⟩
      have finalPosition : final.1.toNat = result.strstart.toNat := by rw [frontier, zeroNat, Nat.sub_zero]
      rw [← finalPosition]
      exact formA
  · have small : d.lookahead.toNat + d.insert.toNat < 3 := by
      have guard : ¬ MIN_MATCH_u.toNat ≤ (d.lookahead + d.insert).toNat := by
        intro ge
        exact enter (UInt32.le_iff_toNat_le.mpr ge)
      rw [sum] at guard
      change ¬ 3 ≤ _ at guard
      omega
    refine ⟨h, d, ?_, good, chains, rfl, rfl, ?_, ?_, ByteFrame.refl h _, Shape.refl h,
      ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩
    · rw [fill_prime_pending_source]
      simp only [bind_app, ldDeflateState_tab good.live.hs, enter, ite_false, pure_app]
    · omega
    · intro large
      omega

/-! ## The read, the padding and the slide -/

theorem pending_read_vchains_any {v : TabView} {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : VHeapChains v h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    VHeapChains v (pendingReadHeapAny h r ds w z d ref io ia wa) (pendingReadState d n) top := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  have counts := resume_read_counts good win get range
  have extent := window_extent good win get
  have fit : fillEnd d + n.toNat ≤ wa.size := by
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := fill_more_nat good win get range
    have nCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
    omega
  have wrote := vheap_window_write (wa' := copied) chains win get
    (fun i hi => copy_range_prefix wa ia (fillEnd d) io n.toNat fit i hi)
  obtain ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, hbytes, hprev, hhead, H⟩ := wrote
  refine ⟨wb, pb, qb, bytes, prev, head, hw, hp, hq, ?_, ?_, ?_, ?_⟩
  · simpa only [pendingReadHeapAny, setD_bytes, ZStreamRef.put_bytes] using hbytes
  · simpa only [pendingReadHeapAny, setD_words, ZStreamRef.put_words] using hprev
  · simpa only [pendingReadHeapAny, setD_words, ZStreamRef.put_words] using hhead
  · apply view_mono H (Nat.le_refl top)
    change fillEnd d ≤ d.strstart.toNat + (d.lookahead + n).toNat
    rw [counts.2.1]
    dsimp only [fillEnd]
    omega

theorem padded_vchains {v : TabView} {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : VHeapChains v h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    VHeapChains v (paddedHeap h ds w d wa) (paddedState d) top := by
  have wrote := vheap_window_write chains win get (padded_prefix good win get range)
  obtain ⟨wb, p, q, bytes, pa, qa, hw, hp, hq, hb, hpa, hqa, H⟩ := wrote
  exact ⟨wb, p, q, bytes, pa, qa, hw, hp, hq, hb, hpa, hqa, H⟩

theorem slide_heap_vchains {v : TabView} {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : ViewChains v (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size top (fillEnd d))
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (head : ∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i)
    (prev : ∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) :
    VHeapChains v (slideHeap h ds w p q d wa pa' qa') (slideState d) (top - d.w_size.toNat) := by
  have counts := fill_slide_counts good env.win env.wbytes range taken
  have sizes := slide_window_sizes good
  have slid := view_slide (h2 := wfn qa') (p2 := wfn pa') (w' := bfn (slideWindow d wa))
    chains good.inv.wsize (by omega)
    (fun i bound => by rw [head i, if_pos bound])
    (fun i bound => by rw [prev i, if_pos bound])
    (slide_window_view good env.win env.wbytes range taken)
  refine ⟨w, p, q, slideWindow d wa, pa', qa', env.win, env.prevp, env.headp,
    ?_, ?_, ?_, ?_⟩
  · simp [slideHeap]
  · simp [slideHeap, setW]
  · simp [slideHeap, setW, upd_ne _ _ _ _ env.hne]
  · change ViewChains v (wfn qa') (wfn pa') (bfn (slideWindow d wa)) d.hash_size d.hash_shift d.hash_mask
      d.w_size (top - d.w_size.toNat) (fillEnd (slideState d))
    rw [counts.2.2.2.2.2.1]
    exact slid

end Zlib.Deflate.Engine.Proofs
