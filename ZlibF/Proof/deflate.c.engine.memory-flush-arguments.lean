import ZlibF.Proof.«deflate.c.engine.flush-arguments»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem memory_stored_length {h : Heap} {ds pb : Nat}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1) :
    let value := (d.strstart.toNat : Int) - d.block_start.toInt
    lsub d.strstart.toUInt64.toInt64 d.block_start = pure (Int64.ofInt value) ∧
      (Int64.ofInt value).toUInt64.toNat = value.toNat ∧
      (Int64.ofInt value).toUInt64.toNat ≤ 4294967296 := by
  have end_ := trees.base.sym_end
  have symbols := ledger.count
  have symbolBound : xs.length ≤ 32767 := by have capacity := trees.base.lit_hi; omega
  have representedBound := represented_le ledger.valid
  have valueLo : 0 ≤ (d.strstart.toNat : Int) - d.block_start.toInt := by
    unfold BlockBalance at balance
    omega
  have valueHi : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 8453887 := by
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


theorem memory_flush_arguments {h : Heap} {r : ZStreamRef} {ds pb w : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (ledger : SymbolLedger buf d xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0) :
    flushOnlyArguments (some (.tab ds)) h =
      .ok ((defaultStoredSource d w, UInt64.ofNat (represented xs)), h) := by
  have difference := memory_stored_length trees ledger trees.run.sym_next_le balance (by omega) (by omega)
  dsimp only at difference
  have delta : ((d.strstart.toNat : Int) - d.block_start.toInt).toNat = represented xs := by
    unfold BlockBalance at balance
    omega
  have sizeBound := difference.2.2
  rw [difference.2.1, delta] at sizeBound
  have word : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64 =
      UInt64.ofNat (represented xs) := by
    apply UInt64.toNat_inj.mp
    rw [difference.2.1, delta, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  unfold flushOnlyArguments
  rw [bind_app, ldDeflateState_tab good.live.hs]
  by_cases nonnegative : 0 ≤ d.block_start.toInt
  · have bound : d.block_start.toInt.toNat ≤ window.size :=
      Nat.le_trans (Nat.le_add_right _ _) (stored_window_readable good win get range balance nonnegative)
    have size := window_extent good win get
    have cast : d.block_start.toUInt64.toUInt32.toNat = d.block_start.toInt.toNat := by
      rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le (show 0 ≤ d.block_start from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative)]
      change d.block_start.toInt.toNat % 4294967296 = d.block_start.toInt.toNat
      exact Nat.mod_eq_of_lt (by omega)
    have add := padd_ok' (r := BRef.blk w) (a := window) (off := 0)
      (n := d.block_start.toUInt64.toUInt32.toNat) get (by rw [cast]; omega)
    change (do
      let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
      let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
      return (source, length.toUInt64)) h = _
    rw [if_pos (show d.block_start ≥ 0 from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), win, bind_app, add]
    rw [difference.1]
    simp only [bind_app, pure_app, cast, Nat.zero_add, word, defaultStoredSource, nonnegative, ite_true]
  · change (do
      let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
      let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
      return (source, length.toUInt64)) h = _
    rw [if_neg (show ¬ d.block_start ≥ 0 from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), difference.1]
    simp only [bind_app, pure_app, word, defaultStoredSource, nonnegative, ite_false]

end Zlib.Deflate.Engine.Proofs

#print axioms Zlib.Deflate.Engine.Proofs.memory_stored_length

#print axioms Zlib.Deflate.Engine.Proofs.memory_flush_arguments
