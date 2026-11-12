import ZlibF.Proof.«deflate.c.engine.insert-chains»
import ZlibF.Proof.«deflate.c.engine.pos-chains»

/-! # Actual hash insertion and the positional chains

`insert_string_pos` is `insert_string_chains` for `PosChains`: no rolling-hash form, no data bound and no key
fact are needed. The key is whatever `INSERT_STRING` computes; it is below `hash_size` because the hash is
masked. `insert_string_walk` adds the walk fact that `longest_match` needs when the insertion is at the
frontier (`top = stop = str`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- `INSERT_STRING(s, str, hash_head)` keeps the positional chains. -/
theorem insert_string_pos {h : Heap} {sr wb hb pb top stop top' stop' bits : Nat}
    {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (hd : h.dstates sr = some d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : PosChains (wfn ha) (wfn pa) d.hash_size d.w_size.toNat top stop)
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (fit : str.toNat + 2 < wa.size) (position : str.toNat < 65536)
    (htop : top ≤ top') (hstr : str.toNat < top') (hfront : stop ≤ str.toNat)
    (hstop : ∀ p, p < stop' → p ≠ str.toNat → p < stop) :
    ∃ key : UInt32,
      let d' := { d with ins_h := key }
      let pa' := pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)
      let h' := { h with
        dstates := upd h.dstates sr (some d')
        words := upd (upd h.words pb (some pa')) hb (some (ha.set! key.toNat str.toUInt16)) }
      INSERT_STRING (some (.tab sr)) str h = .ok ((wfn ha key.toNat).toUInt32, h') ∧
      key.toNat < d.hash_size.toNat ∧
      PosChains (wfn (ha.set! key.toNat str.toUInt16)) (wfn pa') d.hash_size d.w_size.toNat top' stop' ∧
      (∀ i, i ≠ str.toNat &&& (d.w_size.toNat - 1) → wfn pa' i = wfn pa i) := by
  obtain ⟨key, _, keyBound, run⟩ := INSERT_STRING_ok hd env str fit (by omega)
  have s16 : str.toUInt16.toNat = str.toNat := by
    rw [UInt32.toNat_toUInt16, Nat.mod_eq_of_lt position]
  have slot : (str &&& d.w_mask).toNat < pa.size := by
    rw [UInt32.toNat_and]
    have bound := Nat.and_le_right (n := str.toNat) (m := d.w_mask.toNat)
    have size := env.wsize
    have small := env.wmask
    omega
  have headFit : key.toNat < ha.size := by have size := env.hsize; omega
  have prevSet : ∀ i, wfn (pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)) i =
      if i = str.toNat &&& (d.w_size.toNat - 1) then wfn ha key.toNat else wfn pa i := fun i => by
    simpa only [UInt32.toNat_and, mask] using wfn_set pa (str &&& d.w_mask).toNat (wfn ha key.toNat) slot i
  have H := pos_insert chains ws keyBound s16 htop hstr hfront hstop
    (fun i => wfn_set ha key.toNat str.toUInt16 headFit i) prevSet
  refine ⟨key, run, keyBound, H, fun i ne => ?_⟩
  rw [prevSet, ite_eq_right ne]

/-- The walk fact after an insertion at the frontier: with `top = stop = str` before, every position on the
chain that `longest_match` walks from the returned old head `c` (`1 ≤ c`, `str - c ≤ MAX_DIST`) is in
`[1, str)`. -/
theorem insert_walk {ha pa pa' : Nat → UInt16} {n : UInt32} {ws bits str key c : Nat}
    (chains : PosChains ha pa n ws str str) (hws : ws = 2 ^ bits) (big : 262 ≤ ws)
    (keyBound : key < n.toNat) (old : (ha key).toNat = c)
    (same : ∀ i, i ≠ str &&& (ws - 1) → pa' i = pa i)
    (nonzero : 1 ≤ c) (distance : str - c ≤ ws - 262) :
    ∀ p, Chain pa' (ws - 1) (lmLimit str (ws - 262)) c p → 1 ≤ p ∧ p < str :=
  chain_pos_ok chains hws big keyBound old same nonzero distance

end Zlib.Deflate.Engine.Proofs
