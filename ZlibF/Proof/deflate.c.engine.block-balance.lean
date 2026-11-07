import ZlibF.Proof.«deflate.c.engine.symbol-ledger»
import ZlibF.Proof.«deflate.c.engine.advance»

/-! # Signed block positions from the actual symbol ledger

The credit counts bytes already traversed but not yet represented by
stored symbols. Intermediate tally cutpoints may have negative credit.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def BlockBalance (d : DeflateState) (xs : List Symbol) (credit : Int) : Prop :=
  (d.strstart.toNat : Int) - d.block_start.toInt = (represented xs : Int) + credit

theorem initialized_block_balance {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d) :
    BlockBalance d [] 0 := by
  simp [BlockBalance, represented, start.start, start.blockStart]

theorem balance_literal {d : DeflateState} {xs : List Symbol} {credit : Int}
    (balance : BlockBalance d xs credit) (c : UInt8) :
    BlockBalance (literalState d c) (xs ++ [⟨0, c.toNat⟩]) (credit - 1) := by
  unfold BlockBalance at balance ⊢
  simp only [literalState, represented_snoc, Symbol.bytes, ite_true]
  omega

theorem balance_match {d : DeflateState} {xs : List Symbol} {credit : Int}
    (balance : BlockBalance d xs credit) (distance length : UInt32)
    (positive : 1 ≤ distance.toNat) :
    BlockBalance (matchSymbolState d distance length)
      (xs ++ [⟨distance.toNat, length.toNat⟩]) (credit - (length.toNat + 3 : Nat)) := by
  have nonzero : distance.toNat ≠ 0 := by omega
  unfold BlockBalance at balance ⊢
  simp only [matchSymbolState, matchFrequencies, represented_snoc, Symbol.bytes,
    if_neg nonzero]
  omega

/-- The actual one-byte advance repays one byte of credit. -/
theorem balance_advance_one {h : Heap} {ds : Nat} {d : DeflateState}
    {xs : List Symbol} {credit : Int}
    (inv : DStInv h ds d) (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) (balance : BlockBalance d xs credit) :
    BlockBalance (advanceOne d) xs (credit + 1) := by
  have counts := advance_one_counts inv range positive
  unfold BlockBalance at balance ⊢
  rw [counts.1]
  change ((d.strstart.toNat + 1 : Nat) : Int) - d.block_start.toInt = _
  omega

/-- The source buffer capacity bounds how far a live block can extend
behind the current window. Negative block_start is permitted. -/
theorem block_start_bounds {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} {credit : Int} (base : TreesBase h ds d b buf)
    (ledger : SymbolLedger buf d xs) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1) :
    -8453887 ≤ d.block_start.toInt ∧ d.block_start.toInt ≤ d.strstart.toNat := by
  have symbols := ledger.count
  have cap := base.lit_hi
  have end_ := base.sym_end
  have bytes := represented_le ledger.valid
  unfold BlockBalance at balance
  omega

/-- The checked subtraction in fill_window's slide cannot overflow once
the real ledger, block balance and window range hold. -/
theorem block_start_slide_run {h : Heap} {r : ZStreamRef} {ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (good : DGood h r ds z d) (base : TreesBase h ds d b buf)
    (ledger : SymbolLedger buf d xs) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    let value := d.block_start.toInt - (d.w_size.toNat : Int)
    lsub d.block_start d.w_size.toUInt64.toInt64 = pure (Int64.ofInt value) ∧
      (Int64.ofInt value).toInt = value := by
  have bounds := block_start_bounds base ledger count balance lo hi
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have wsz := good.inv.wsz
  have cast : d.w_size.toUInt64.toInt64.toInt = (d.w_size.toNat : Int) := by
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp
      omega
  dsimp only
  have valueLo : -9223372036854775808 ≤ d.block_start.toInt - (d.w_size.toNat : Int) := by omega
  have valueHi : d.block_start.toInt - (d.w_size.toNat : Int) ≤ 9223372036854775807 := by omega
  refine ⟨?_, ?_⟩
  · unfold lsub chk64
    rw [cast]
    simp only [valueLo, valueHi, and_self, if_true]
  · rw [Int64.toInt_ofInt]
    exact Int.bmod_eq_of_le (by change -9223372036854775808 ≤ _; omega)
      (by change _ < 9223372036854775808; omega)

/-- The position updates used by a slide preserve the balance, including
when the signed block position crosses zero. -/
theorem balance_slide {d result : DeflateState} {xs : List Symbol} {credit : Int}
    (balance : BlockBalance d xs credit) (start : d.w_size.toNat ≤ d.strstart.toNat)
    (position : result.strstart = d.strstart - d.w_size)
    (block : result.block_start.toInt = d.block_start.toInt - (d.w_size.toNat : Int)) :
    BlockBalance result xs credit := by
  have sub : result.strstart.toNat = d.strstart.toNat - d.w_size.toNat := by
    rw [position, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr start)]
  unfold BlockBalance at balance ⊢
  rw [sub, block]
  omega

end Zlib.Deflate.Engine.Proofs
