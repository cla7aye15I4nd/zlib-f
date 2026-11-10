import ZlibF.Proof.«trees.c.stored-format»
import ZlibF.Proof.«deflate.c.engine.content-boundary»
import ZlibF.Proof.«deflate.c.engine.stored-length»

/-! # A stored window slice is exactly the same accepted input as the symbol block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (sourceBytes)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A byte slice of the actual window agrees with logical input. The
nonnegative block position is the real source-pointer branch condition.
The flush cutpoint has zero byte credit; half-finished tally/advance
states with a deferred byte do not satisfy that cutpoint relation. -/
theorem stored_window_input {d : DeflateState} {window : Array UInt8} {input : Nat → UInt8}
    {origin base : Nat} {xs : List Symbol}
    (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (nonnegative : 0 ≤ d.block_start.toInt)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) :
    sourceBytes window d.block_start.toInt.toNat (represented xs) =
      (List.range (represented xs)).map (fun i => input (base + i)) := by
  have start : d.block_start.toInt.toNat + represented xs = d.strstart.toNat := by
    unfold BlockBalance at balance
    omega
  have position : origin + d.block_start.toInt.toNat = base := by omega
  unfold sourceBytes
  apply List.map_congr_left
  intro i member
  have fit := List.mem_range.mp member
  have same := view (d.block_start.toInt.toNat + i) (by dsimp only [fillEnd]; omega)
  rw [← Nat.add_assoc, position] at same
  simpa only [Array.getElem!_eq_getD, show (default : UInt8) = 0 from rfl, bfn] using same

/-- Independent stored decoding extends exactly the already accepted
input prefix, using the bytes at the actual block_start window offset. -/
theorem stored_window_prefix {d : DeflateState} {window : Array UInt8} {input : Nat → UInt8}
    {origin base : Nat} {xs : List Symbol}
    (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (nonnegative : 0 ≤ d.block_start.toInt)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) :
    inputPrefix input base ++ sourceBytes window d.block_start.toInt.toNat (represented xs) =
      inputPrefix input (base + represented xs) := by
  rw [stored_window_input balance accounted nonnegative view]
  simp only [inputPrefix, List.range_add, List.map_append, List.map_map]
  rfl

/-- The real nonnegative source slice is readable up to strstart. Its
extent follows from the initialized window allocation and current range. -/
theorem stored_window_readable {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {window : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (nonnegative : 0 ≤ d.block_start.toInt) :
    d.block_start.toInt.toNat + represented xs ≤ window.size := by
  have size := (window_extent good win get).1
  unfold BlockBalance at balance
  dsimp only [fillEnd] at range
  omega

end Zlib.Deflate.Engine.Proofs
