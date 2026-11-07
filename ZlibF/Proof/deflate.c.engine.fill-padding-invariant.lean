import ZlibF.Proof.«deflate.c.engine.fill-high-water»

/-! # Padding preserves valid input, representation and chains -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem padding_target_small {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) : paddingTarget d < 2 ^ 64 := by
  have extent := window_extent good win get
  have bounds := padding_bounds d range good.inv.hw
  omega

theorem padded_good {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    DGood (paddedHeap h ds w d wa) r ds z (paddedState d) := by
  have bounds := padding_bounds d range good.inv.hw
  have small := padding_target_small good win get range
  have high : (paddedState d).high_water.toNat ≤ d.window_size.toNat := by
    change (UInt64.ofNat (paddingTarget d)).toNat ≤ _
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
    exact bounds.2.2.2.1
  let array := fillRange wa (paddingStart d) (paddingCount d) 0
  let hb := { h with bytes := upd h.bytes w (some array) }
  have bytesGood : DGood hb r ds z d := good.bytes_set w array wa get (size_fillRange _ _ _ _)
  have inv : DStInv hb ds (paddedState d) :=
    { bytesGood.inv with
      hw := high
      blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact bytesGood.setD' (d' := paddedState d) rfl good.live.status inv (by trkeep)

theorem padded_prefix {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (i : Nat) (valid : i < fillEnd d) :
    bfn (fillRange wa (paddingStart d) (paddingCount d) 0) i = bfn wa i := by
  have extent := window_extent good win get
  have bounds := padding_bounds d range good.inv.hw
  have fit : paddingStart d + paddingCount d ≤ wa.size := by omega
  unfold bfn
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    getElem?_fillRange wa (paddingStart d) (paddingCount d) 0 i fit]
  simp [show ¬ paddingStart d ≤ i ∧ i < paddingStart d + paddingCount d by omega]

theorem padded_chains {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    HeapChains (paddedHeap h ds w d wa) (paddedState d) top := by
  have wrote := heap_chains_window_write chains win get (padded_prefix good win get range)
  obtain ⟨wb, p, q, bytes, pa, qa, hw, hp, hq, hb, hpa, hqa, H⟩ := wrote
  exact ⟨wb, p, q, bytes, pa, qa, hw, hp, hq, hb, hpa, hqa, H⟩

theorem padded_form {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (large : 3 ≤ d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    InsHForm (paddedState d).hash_shift (paddedState d).hash_mask
      (bfn (fillRange wa (paddingStart d) (paddingCount d) 0))
      (paddedState d).strstart.toNat (paddedState d).ins_h := by
  change InsHForm d.hash_shift d.hash_mask
    (bfn (fillRange wa (paddingStart d) (paddingCount d) 0)) d.strstart.toNat d.ins_h
  apply form_congr form
  · apply padded_prefix good win get range
    dsimp only [fillEnd]
    omega
  · apply padded_prefix good win get range
    dsimp only [fillEnd]
    omega

theorem padded_initialized {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    min (fillEnd (paddedState d) + 258) (paddedState d).window_size.toNat ≤ (paddedState d).high_water.toNat := by
  have small := padding_target_small good win get range
  change min (fillEnd d + 258) d.window_size.toNat ≤ (UInt64.ofNat (paddingTarget d)).toNat
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  exact (padding_bounds d range good.inv.hw).2.2.2.2.2

end Zlib.Deflate.Engine.Proofs
