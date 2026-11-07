import ZlibF.Proof.«deflate.c.engine.static-budget»
import ZlibF.Proof.«deflate.c.engine.block-balance»

/-! # The real strategy's signed block length cannot wrap the stored comparison -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual subtraction used by FLUSH_BLOCK_ONLY is checked and returns
the ledger's traversed byte count. The default symbol range supplies a
small unsigned result even if block_start has become negative after slides. -/
theorem default_stored_length {h : Heap} {ds pb : Nat}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (memory : d.lit_bufsize.toNat = 16384) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1) :
    let value := (d.strstart.toNat : Int) - d.block_start.toInt
    lsub d.strstart.toUInt64.toInt64 d.block_start = pure (Int64.ofInt value) ∧
      (Int64.ofInt value).toUInt64.toNat = value.toNat ∧
      (Int64.ofInt value).toUInt64.toNat ≤ 4294967296 := by
  have end_ := trees.base.sym_end
  have symbols := ledger.count
  have symbolBound : xs.length ≤ 16383 := by omega
  have representedBound := represented_le ledger.valid
  have valueLo : 0 ≤ (d.strstart.toNat : Int) - d.block_start.toInt := by
    unfold BlockBalance at balance
    omega
  have valueHi : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 4226815 := by
    unfold BlockBalance at balance
    omega
  have startBound := d.strstart.toNat_lt
  have cast : d.strstart.toUInt64.toInt64.toInt = (d.strstart.toNat : Int) := by
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp
      omega
  dsimp only
  have word : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toNat =
      ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    change (BitVec.ofInt 64 ((d.strstart.toNat : Int) - d.block_start.toInt)).toNat = _
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt valueLo (by omega)]
  refine ⟨?_, word, by rw [word]; omega⟩
  unfold lsub chk64
  rw [cast]
  rw [if_pos (show -9223372036854775808 ≤ (d.strstart.toNat : Int) - d.block_start.toInt ∧
    (d.strstart.toNat : Int) - d.block_start.toInt ≤ 9223372036854775807 by omega)]

/-- On the real signed length calculation, selecting stored implies
enough pending room. No caller-supplied length or non-wrapping cost premise
is needed beyond the actual block balance and original ledger. -/
theorem default_stored_position_room {h : Heap} {ds pb : Nat}
    {d prepared : DeflateState} {buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (memory : d.lit_bufsize.toNat = 16384) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (budget : prepared.static_len.toNat ≤ 31 * xs.length + 7)
    (selected : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64 + (4 : UInt64) ≤
      ZlibF.Math.DeflateSelection.selectedCost (((prepared.opt_len + 3 + 7) >>> 3))
        (((prepared.static_len + 3 + 7) >>> 3)) (prepared.strategy == Z_FIXED)) :
    ((d.strstart.toNat : Int) - d.block_start.toInt).toNat + 6 ≤ 63488 := by
  have length := default_stored_length trees ledger memory count balance lo hi
  have room := default_stored_selection_room trees ledger memory count budget length.2.2 selected
  rw [length.2.1] at room
  exact room

end Zlib.Deflate.Engine.Proofs
