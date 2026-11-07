import ZlibF.Proof.«deflate.c.engine.fill-initial»
import ZlibF.Proof.«deflate.c.engine.fill-read»

/-! # The high-water write after the first nonempty read -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def firstPadding (n : UInt32) : UInt64 :=
  if (65536 : UInt64) - n.toUInt64 > WIN_INIT_u then WIN_INIT_u else 65536 - n.toUInt64

theorem firstPadding_nat (n : UInt32) (bound : n.toNat ≤ 65536) :
    (firstPadding n).toNat = min (65536 - n.toNat) 258 := by
  have sub : ((65536 : UInt64) - n.toUInt64).toNat = 65536 - n.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using bound)]
    simp
  unfold firstPadding
  split
  · rename_i large
    change WIN_INIT_u < (65536 : UInt64) - n.toUInt64 at large
    rw [UInt64.lt_iff_toNat_lt, sub] at large
    change 258 < 65536 - n.toNat at large
    simpa only [show WIN_INIT_u.toNat = 258 from rfl] using (Nat.min_eq_right (by omega)).symm
  · rename_i small
    change ¬ WIN_INIT_u < (65536 : UInt64) - n.toUInt64 at small
    rw [UInt64.lt_iff_toNat_lt, sub] at small
    change ¬ 258 < 65536 - n.toNat at small
    rw [sub, Nat.min_eq_left (by omega)]

theorem fill_high_water_first {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (hw : d.high_water = 0) (wsz : d.window_size = 65536)
    (nonzero : d.lookahead ≠ 0) (bound : d.lookahead.toNat ≤ 65536) :
    fillHighWater (some (.tab ds)) h = .ok ((),
      setD { h with
        bytes := upd h.bytes w (some (fillRange wa d.lookahead.toNat (firstPadding d.lookahead).toNat 0)) }
        ds { d with high_water := d.lookahead.toUInt64 + firstPadding d.lookahead }) := by
  let n := d.lookahead
  let pad := firstPadding n
  have padNat := firstPadding_nat n bound
  change pad.toNat = min (65536 - n.toNat) 258 at padNat
  change n.toNat ≤ 65536 at bound
  have fit : n.toNat + pad.toNat ≤ wa.size := by omega
  have padSmall : pad.toNat < 2 ^ 32 := by omega
  have cast : pad.toUInt32.toNat = pad.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt padSmall]
  have pos : (0 : UInt64) < n.toUInt64 := by
    rw [UInt64.lt_iff_toNat_lt]
    have nz : n.toNat ≠ 0 := by intro eq; apply nonzero; exact UInt32.toNat_inj.mp eq
    simpa using (show 0 < n.toNat by omega)
  have add : padd d.window d.lookahead.toNat h = .ok (.ref (.blk w) n.toNat, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : 0 + n.toNat ≤ wa.size)
  have fill : memsetB (.ref (.blk w) n.toNat) 0 pad.toNat h =
      .ok ((), { h with bytes := upd h.bytes w (some (fillRange wa n.toNat pad.toNat 0)) }) := by
    exact Ptr.fill_ok get writable fit
  unfold fillHighWater
  simp only [bind_app, ldDeflateState_tab state]
  simp only [ss, hw, wsz, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.zero_add]
  simp only [show (0 : UInt64) < 65536 from by decide, if_true]
  rw [if_pos pos]
  have samePad : (if (65536 : UInt64) - d.lookahead.toUInt64 > WIN_INIT_u then WIN_INIT_u
      else 65536 - d.lookahead.toUInt64) = pad := rfl
  by_cases large : (65536 : UInt64) - d.lookahead.toUInt64 > WIN_INIT_u
  all_goals simp only [large, if_true, if_false] at samePad ⊢
  all_goals rw [samePad]
  all_goals simp only [UInt32.toNat_toUInt64, cast, bind_app, add, fill, wrD_eq, state]
  all_goals try { rw [add]; simp only []; rw [fill]; simp only [wrD_eq, state] }
  all_goals simp only [ss, hw, wsz, n, pad]

end Zlib.Deflate.Engine.Proofs
