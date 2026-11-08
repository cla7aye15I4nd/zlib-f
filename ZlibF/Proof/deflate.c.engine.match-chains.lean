import ZlibF.Proof.«deflate.c.engine.insert-chains»
import ZlibF.Proof.«deflate.c.engine.lmmain»

/-! # Actual hash tables supply the matcher's chain environment

Candidate order is retained from the old head returned by insertion.
It is not inferred from the new NIL head at position zero.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem heap_chains_arrays {h : Heap} {d : DeflateState} {top w p q : Nat}
    {wa : Array UInt8} {pa qa : Array UInt16} (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa) :
    HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat) := by
  obtain ⟨w0, p0, q0, wa0, pa0, qa0, win0, prev0, head0, hw0, hp0, hq0, H⟩ := chains
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using prev0.symm
  have qe : q0 = q := by simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using head0.symm
  subst w0 p0 q0
  have wbytes : wa0 = wa := Option.some.inj (hw0.symm.trans hw)
  have pwords : pa0 = pa := Option.some.inj (hp0.symm.trans hp)
  have qwords : qa0 = qa := Option.some.inj (hq0.symm.trans hq)
  subst wa0 pa0 qa0
  exact H

def insertedHeap (h : Heap) (ds p q : Nat) (d : DeflateState) (pa qa : Array UInt16) (key : UInt32) : Heap :=
  { h with
    dstates := upd h.dstates ds (some { d with ins_h := key }),
    words := upd (upd h.words p
      (some (pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat))))
      q (some (qa.set! key.toNat d.strstart.toUInt16)) }

/-- All facts used to enter the matcher are read back from the actual
INSERT_STRING result. The old head supplies candidate order, including
the NIL boundary. The new head and prev cell supply chain provenance. -/
theorem insert_published_chain {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat))
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat)
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

theorem match_environment_published {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (lookahead : 262 ≤ d.lookahead.toNat) (previous : d.prev_length.toNat ≤ 258) :
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
The actual matcher obtains its array and chain bounds from the published
heap invariant. Only match_start changes. The chain and DGood survive.
Candidate order is the fact proved from the pre-insertion head.
-/
theorem longest_match_chains {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (lookahead : 262 ≤ d.lookahead.toNat) (previous : d.prev_length.toNat ≤ 258) :
    ∃ (len ms : UInt32) (best : Nat),
      longest_match (some (.tab ds)) candidate h = .ok (len, hAt h ds d ms) ∧
      len = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
        (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) ∧
      DGood (hAt h ds d ms) r ds z { d with match_start := ms } ∧
      HeapChains (hAt h ds d ms) { d with match_start := ms } (d.strstart.toNat + 1) := by
  have env := match_environment_published good win prev head hw hp hq chains hash keyBound published
    link nonzero older distance range lookahead previous
  obtain ⟨len, after, ms, best, run, result, eq, lower, upper, matching⟩ := longest_match_ok env
  subst after
  have inv : DStInv h ds { d with match_start := ms } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have kept := good.setD' (d' := { d with match_start := ms }) rfl good.live.status inv (by trkeep)
  refine ⟨len, ms, best, run, result, lower, upper, matching, kept, ?_⟩
  simpa only [HeapChains, hAt, setD] using heapChains

end Zlib.Deflate.Engine.Proofs
