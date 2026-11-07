import ZlibF.Proof.«deflate.c.engine.slow-source»
import ZlibF.Proof.«deflate.c.engine.advance»

/-! # Boundaries of the slow match-consumption loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem window_extent {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    wa.size = d.window_size.toNat ∧ d.window_size.toNat ≤ 65536 := by
  obtain ⟨w0, p, q, b, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  rw [good.inv.wsz]
  exact ⟨size, by omega⟩

/-- Actual insertion with only three bytes of lookahead. The match
consumption loop has less than MIN_LOOKAHEAD after its first counter write.
All byte arrays are unchanged by insertion. -/
theorem current_insert {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (ordered : top ≤ d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key candidate after,
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      DGood after r ds z { d with ins_h := key } ∧
      HeapChains after { d with ins_h := key } (d.strstart.toNat + 1) ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key := by
  obtain ⟨w0, p, q, bytes, prev, head, env, H⟩ := heap_chains_environment good chains
  have wid : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have array : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst bytes
  have extent := window_extent good win get
  have room : d.strstart.toNat + d.lookahead.toNat ≤ wa.size := by omega
  have bound : d.strstart.toNat < 65536 := by omega
  obtain ⟨key, after, run, goodA, chainsA, primed⟩ := insert_string_good_chains good env H d.strstart
    good.inv.wsize good.inv.wmask ordered (by omega) room bound form
  obtain ⟨other, _, _, exactRun⟩ := INSERT_STRING_ok good.live.hs env d.strstart (by omega) (by omega)
  have pair := Except.ok.inj (run.symm.trans exactRun)
  have frame : after.bytes = h.bytes := congrArg (fun x => x.2.bytes) pair
  exact ⟨key, _, after, run, goodA, chainsA, frame, primed⟩

def prepareMatch (d : DeflateState) : DeflateState :=
  { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 }

theorem prepare_match_counts (d : DeflateState)
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (lookahead : 262 ≤ d.lookahead.toNat) :
    (prepareMatch d).lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      (prepareMatch d).prev_length.toNat = d.prev_length.toNat - 2 ∧
      5 ≤ (prepareMatch d).lookahead.toNat ∧
      1 ≤ (prepareMatch d).prev_length.toNat ∧ (prepareMatch d).prev_length.toNat ≤ 256 := by
  have one : (d.prev_length - 1).toNat = d.prev_length.toNat - 1 := u32_sub_one (by omega)
  have count : (d.prev_length - 2).toNat = d.prev_length.toNat - 2 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 2 ≤ _; omega)]
    rfl
  have remaining : (d.lookahead - (d.prev_length - 1)).toNat =
      d.lookahead.toNat - (d.prev_length.toNat - 1) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, one]; omega), one]
  exact ⟨remaining, count, by rw [show (prepareMatch d).lookahead.toNat = _ from remaining]; omega,
    by rw [show (prepareMatch d).prev_length.toNat = _ from count]; omega,
    by rw [show (prepareMatch d).prev_length.toNat = _ from count]; omega⟩

/-- Restricting the valid-data endpoint is safe when every represented
position remains below it with its three hash bytes. -/
theorem chains_restrict {head prev : Nat → UInt16} {bytes : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim newLim : Nat} (chains : HashChains head prev bytes n hsh hm ws top lim)
    (room : top + 2 ≤ newLim) : HashChains head prev bytes n hsh hm ws top newLim := by
  refine ⟨fun k p hk reach nonzero owned => ?_⟩
  obtain ⟨older, _, hash, predecessor⟩ := chains.node k p hk reach nonzero owned
  exact ⟨older, by omega, hash, predecessor⟩

theorem prepare_match_good {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    DGood (setD h ds (prepareMatch d)) r ds z (prepareMatch d) ∧
      HeapChains (setD h ds (prepareMatch d)) (prepareMatch d) (d.strstart.toNat + 1) ∧
      (prepareMatch d).strstart.toNat + (prepareMatch d).prev_length.toNat + 1 +
        (prepareMatch d).lookahead.toNat ≤ d.window_size.toNat := by
  have counts := prepare_match_counts d previous length lookahead
  have inv : DStInv h ds (prepareMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := prepareMatch d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
    exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq,
      chains_restrict H (by change d.strstart.toNat + 1 + 2 ≤ d.strstart.toNat + _; omega)⟩
  · change d.strstart.toNat + (prepareMatch d).prev_length.toNat + 1 +
      (prepareMatch d).lookahead.toNat ≤ d.window_size.toNat
    rw [counts.1, counts.2.1]
    omega

end Zlib.Deflate.Engine.Proofs
