import ZlibF.Proof.«deflate.c.engine.initial»

/-! # Advancing one consumed window byte preserves the engine boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def advanceOne (d : DeflateState) : DeflateState :=
  { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 }

theorem advance_one_counts {h : Heap} {ds : Nat} {d : DeflateState}
    (inv : DStInv h ds d) (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    (advanceOne d).strstart.toNat = d.strstart.toNat + 1 ∧
      (advanceOne d).lookahead.toNat = d.lookahead.toNat - 1 ∧
      (advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat =
        d.strstart.toNat + d.lookahead.toNat := by
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) inv.wbits_hi
         _ = 32768 := by decide
  rw [inv.wsz] at range
  have ss : (d.strstart + 1).toNat = d.strstart.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have la : (d.lookahead - 1).toNat = d.lookahead.toNat - 1 := u32_sub_one positive
  exact ⟨ss, la, by change (d.strstart + 1).toNat + (d.lookahead - 1).toNat = _; rw [ss, la]; omega⟩

/-- A real one-byte consumption step keeps representation, H and the
valid window-data endpoint. The caller supplies the actual range and a
positive lookahead; the machine additions/subtractions are derived. -/
theorem advance_one_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    DGood (setD h ds (advanceOne d)) r ds z (advanceOne d) ∧
      HeapChains (setD h ds (advanceOne d)) (advanceOne d) top ∧
      (advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat ≤ (advanceOne d).window_size.toNat := by
  have counts := advance_one_counts good.inv range positive
  have inv : DStInv h ds (advanceOne d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := advanceOne d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
    refine ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, ?_⟩
    change HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask d.w_size.toNat top
      ((advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat)
    rw [counts.2.2]
    exact H
  · rw [counts.2.2]
    exact range

theorem advance_one_padding {h : Heap} {ds : Nat} {d : DeflateState}
    (inv : DStInv h ds d) (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat) :
    min ((advanceOne d).strstart.toNat + (advanceOne d).lookahead.toNat + 258)
      (advanceOne d).window_size.toNat ≤ (advanceOne d).high_water.toNat := by
  rw [(advance_one_counts inv range positive).2.2]
  exact padded

end Zlib.Deflate.Engine.Proofs
