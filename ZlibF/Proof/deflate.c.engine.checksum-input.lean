import ZlibF.Proof.«deflate.c.engine.fill-checksum»
import ZlibF.Proof.«deflate.c.engine.fill-history»
import ZlibF.Math.DeflateSymbolTrace

/-! # The checksum input ledger agrees with the logical compression input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateChecksum
set_option autoImplicit false

/-- The array slice is precisely its bounded pointwise byte view. -/
theorem checksum_input_array_slice (incoming : Array UInt8) (offset count : Nat)
    (fit : offset + count ≤ incoming.size) :
    (List.range count).map (fun j => bfn incoming (offset + j)) =
      (incoming.toList.drop offset).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      List.length_drop, Array.length_toList]
    omega
  · intro j left right
    have index : j < count := by simpa only [List.length_map, List.length_range] using left
    have bound : offset + j < incoming.size := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, Array.getElem_toList]
    exact (getElem_bfn incoming (offset + j) bound).symm

/-- Agreement before the old endpoint and the actual new caller bytes
determine the entire next accepted input prefix. -/
theorem checksum_input_prefix_append {input extended : Nat → UInt8}
    {limit offset count : Nat} {incoming : Array UInt8}
    (agree : ∀ i, i < limit → extended i = input i)
    (added : ∀ j, j < count → extended (limit + j) = bfn incoming (offset + j))
    (fit : offset + count ≤ incoming.size) :
    inputPrefix extended (limit + count) =
      inputPrefix input limit ++ (incoming.toList.drop offset).take count := by
  unfold inputPrefix
  rw [List.range_add, List.map_append, List.map_map]
  have old : (List.range limit).map extended = (List.range limit).map input := by
    apply List.map_congr_left
    intro i member
    exact agree i (List.mem_range.mp member)
  rw [old]
  congr 1
  calc
    (List.range count).map (extended ∘ (limit + ·)) =
        (List.range count).map (fun j => bfn incoming (offset + j)) := by
      apply List.map_congr_left
      intro j member
      exact added j (List.mem_range.mp member)
    _ = _ := checksum_input_array_slice incoming offset count fit

/-- The actual refill extension function joins the same caller bytes to
the previously accepted input used by independent raw block encoding. -/
theorem checksum_extend_input_prefix (input : Nat → UInt8) (limit : Nat)
    (incoming : Array UInt8) (offset count : Nat) (fit : offset + count ≤ incoming.size) :
    inputPrefix (extendInput input limit incoming offset) (limit + count) =
      inputPrefix input limit ++ (incoming.toList.drop offset).take count := by
  apply checksum_input_prefix_append
  · intro i before
    simp only [extendInput, before, ite_true]
  · intro j _before
    simp only [extendInput, show ¬ limit + j < limit from by omega, ite_false,
      Nat.add_sub_cancel_left]
  · exact fit

end Zlib.Deflate.Engine.Proofs
