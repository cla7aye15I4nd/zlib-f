import ZlibF.Proof.«deflate.c.engine.match-insert-loop»

/-! # Saved valid-data endpoint during short match consumption

The C reduces lookahead before advancing strstart. Hash bytes remain valid
up to the old endpoint during these intermediate states.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- Actual hash arrays with an explicit valid-data endpoint. This is an
internal consumption boundary, not an additional public precondition. -/
def HeapChainsAt (h : Heap) (d : DeflateState) (top validEnd : Nat) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top validEnd

theorem HeapChains.at {h : Heap} {d : DeflateState} {top : Nat}
    (chains : HeapChains h d top) :
    HeapChainsAt h d top (d.strstart.toNat + d.lookahead.toNat) := chains

theorem HeapChainsAt.collapse {h : Heap} {d : DeflateState} {top validEnd : Nat}
    (chains : HeapChainsAt h d top validEnd)
    (endpoint : validEnd = d.strstart.toNat + d.lookahead.toNat) :
    HeapChains h d top := by rw [endpoint] at chains; exact chains

theorem HeapChainsAt.raise {h : Heap} {d : DeflateState} {top top' validEnd : Nat}
    (chains : HeapChainsAt h d top validEnd) (ordered : top ≤ top') :
    HeapChainsAt h d top' validEnd := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq,
    chains_mono H ordered (Nat.le_refl validEnd)⟩

theorem HeapChainsAt.keep {h h' : Heap} {d e : DeflateState} {top validEnd : Nat}
    (chains : HeapChainsAt h d top validEnd)
    (bytes : h'.bytes = h.bytes) (words : h'.words = h.words)
    (win : e.window = d.window) (prev : e.prev = d.prev) (head : e.head = d.head)
    (size : e.hash_size = d.hash_size) (shift : e.hash_shift = d.hash_shift)
    (mask : e.hash_mask = d.hash_mask) (window : e.w_size = d.w_size) :
    HeapChainsAt h' e top validEnd := by
  obtain ⟨w, p, q, wa, pa, qa, dw, dp, dq, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win.trans dw, prev.trans dp, head.trans dq,
    by rw [bytes]; exact hw, by rw [words]; exact hp, by rw [words]; exact hq,
    by simpa only [size, shift, mask, window] using H⟩

theorem heap_chains_at_environment {h : Heap} {r : ZStreamRef} {ds top validEnd : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : HeapChainsAt h d top validEnd) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa ∧
      HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
        d.w_size.toNat top validEnd := by
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

theorem insert_string_chains_at {h : Heap} {sr wb hb pb top bits validEnd : Nat}
    {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (hd : h.dstates sr = some d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top validEnd)
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ validEnd)
    (window : validEnd ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key : UInt32,
      let d' := { d with ins_h := key }
      let h' := { h with
        dstates := upd h.dstates sr (some d')
        words := upd (upd h.words pb (some (pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat))))
          hb (some (ha.set! key.toNat str.toUInt16)) }
      INSERT_STRING (some (.tab sr)) str h = .ok ((wfn ha key.toNat).toUInt32, h') ∧
      HeapChainsAt h' d' (str.toNat + 1) validEnd ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  have fit : str.toNat + 2 < wa.size := by omega
  obtain ⟨key, keyEq, keyBound, run⟩ := INSERT_STRING_ok hd env str fit (by omega)
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
  have H := chains_insert chains ws ordered data
    (show (hkey d.hash_shift d.hash_mask (bfn wa) str.toNat).toNat = key.toNat by rw [hash])
    keyBound s16
    (fun i => wfn_set ha key.toNat str.toUInt16 headFit i)
    (fun i => by
      simpa only [UInt32.toNat_and, mask] using
        wfn_set pa (str &&& d.w_mask).toNat (wfn ha key.toNat) slot i)
  refine ⟨key, run, ?_, ?_⟩
  · refine ⟨wb, pb, hb, wa, pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat),
      ha.set! key.toNat str.toUInt16, env.win, env.prevp, env.headp, ?_, ?_, ?_, ?_⟩
    · exact env.wbytes
    · simp [upd_ne _ _ _ _ env.hne.symm]
    · simp
    · simpa only [UInt32.toNat_and, mask] using H
  · rw [keyEq, byte]
    exact form_next form

/-- The same actual insertion preserves both representation and chains.
This is the combined caller boundary needed by the engine loop. -/
theorem insert_string_good_chains_at {h : Heap} {r : ZStreamRef} {sr wb hb pb top bits validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : DGood h r sr z d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top validEnd)
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ validEnd)
    (window : validEnd ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after, INSERT_STRING (some (.tab sr)) str h =
        .ok ((wfn ha key.toNat).toUInt32, after) ∧
      DGood after r sr z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (str.toNat + 1) validEnd ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  obtain ⟨key, run, H, primed⟩ := insert_string_chains_at good.live.hs env chains str ws mask
    ordered data window position form
  let pa' := pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)
  let ha' := ha.set! key.toNat str.toUInt16
  have prevGood := good.words_set pb pa' pa env.pwords (by simp [pa'])
  have headGood := prevGood.words_set hb ha' ha
    (by simpa [env.hne] using env.hwords) (by simp [ha'])
  have inv : DStInv _ sr { d with ins_h := key } :=
    { headGood.inv with blocks := headGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have updated := headGood.setD' (d' := { d with ins_h := key }) rfl good.live.status inv (by trkeep)
  refine ⟨key, _, run, ?_, H, primed⟩
  exact updated


theorem current_insert_storage_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (ordered : top ≤ d.strstart.toNat)
    (range : validEnd ≤ d.window_size.toNat)
    (data : d.strstart.toNat + 3 ≤ validEnd)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key candidate after,
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      DGood after r ds z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (d.strstart.toNat + 1) validEnd ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) := by
  obtain ⟨w0, p, q, bytes, prev, head, env, H⟩ := heap_chains_at_environment good chains
  have wid : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have array : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst bytes
  have extent := window_extent good win get
  have room : validEnd ≤ wa.size := by omega
  have bound : d.strstart.toNat < 65536 := by omega
  obtain ⟨key, after, run, goodA, chainsA, primed⟩ := insert_string_good_chains_at good env H d.strstart
    good.inv.wsize good.inv.wmask ordered (by omega) room bound form
  obtain ⟨other, _, _, exactRun⟩ := INSERT_STRING_ok good.live.hs env d.strstart (by omega) (by omega)
  have pair := Except.ok.inj (run.symm.trans exactRun)
  have frame : after.bytes = h.bytes := congrArg (fun x => x.2.bytes) pair
  exact ⟨key, _, after, run, goodA, chainsA, frame, primed,
    insert_string_byte_frame good.live.hs env d.strstart (by omega) (by omega) run⟩


/-- The two actual counter subtractions need only the selected match's
real remaining bytes. They do not require MIN_LOOKAHEAD. -/
theorem prepare_match_counts_bounded (d : DeflateState)
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (available : d.prev_length.toNat - 1 ≤ d.lookahead.toNat) :
    (prepareMatch d).lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      (prepareMatch d).prev_length.toNat = d.prev_length.toNat - 2 ∧
      1 ≤ (prepareMatch d).prev_length.toNat ∧ (prepareMatch d).prev_length.toNat ≤ 256 ∧
      (prepareMatch d).strstart.toNat + (prepareMatch d).prev_length.toNat + 1 +
        (prepareMatch d).lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
  have one : (d.prev_length - 1).toNat = d.prev_length.toNat - 1 := u32_sub_one (by omega)
  have count : (d.prev_length - 2).toNat = d.prev_length.toNat - 2 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 2 ≤ _; omega)]
    rfl
  have remaining : (d.lookahead - (d.prev_length - 1)).toNat =
      d.lookahead.toNat - (d.prev_length.toNat - 1) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, one]; exact available), one]
  refine ⟨remaining, count, ?_, ?_, ?_⟩
  · change 1 ≤ (d.prev_length - 2).toNat
    rw [count]; omega
  · change (d.prev_length - 2).toNat ≤ 256
    rw [count]; omega
  · change d.strstart.toNat + (d.prev_length - 2).toNat + 1 +
      (d.lookahead - (d.prev_length - 1)).toNat = _
    rw [remaining, count]; omega

/-- Reducing lookahead retains the original valid-data endpoint. -/
theorem prepare_match_good_at {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (available : d.prev_length.toNat - 1 ≤ d.lookahead.toNat) :
    DGood (setD h ds (prepareMatch d)) r ds z (prepareMatch d) ∧
      HeapChainsAt (setD h ds (prepareMatch d)) (prepareMatch d)
        (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat) ∧
      1 ≤ (prepareMatch d).prev_length.toNat ∧ (prepareMatch d).prev_length.toNat ≤ 256 ∧
      (prepareMatch d).strstart.toNat + (prepareMatch d).prev_length.toNat + 1 +
        (prepareMatch d).lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
  have counts := prepare_match_counts_bounded d previous length available
  have inv : DStInv h ds (prepareMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨good.setD' (d' := prepareMatch d) rfl good.live.status inv (by trkeep),
    chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    counts.2.2.1, counts.2.2.2.1, counts.2.2.2.2⟩

theorem bump_start_good_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat) :
    (bumpStart d).strstart.toNat = d.strstart.toNat + 1 ∧
      DGood (setD h ds (bumpStart d)) r ds z (bumpStart d) ∧
      HeapChainsAt (setD h ds (bumpStart d)) (bumpStart d) top validEnd := by
  have extent := window_extent good win get
  have ss : (bumpStart d).strstart.toNat = d.strstart.toNat + 1 := by
    change (d.strstart + 1).toNat = _
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have inv : DStInv h ds (bumpStart d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨ss, good.setD' (d' := bumpStart d) rfl good.live.status inv (by trkeep),
    chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem count_down_good_at {h : Heap} {r : ZStreamRef} {ds top validEnd : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChainsAt h d top validEnd) :
    DGood (setD h ds (countDown d)) r ds z (countDown d) ∧
      HeapChainsAt (setD h ds (countDown d)) (countDown d) top validEnd := by
  have inv : DStInv h ds (countDown d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨good.setD' (d' := countDown d) rfl good.live.status inv (by trkeep),
    chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

end Zlib.Deflate.Engine.Proofs
