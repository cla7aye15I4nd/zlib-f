import ZlibF.Proof.«trees.c.runs»

/-! # The bit sequence written by the dynamic-header routine

This describes the writer's wire bits. The independent format grammar is
separate from this model.
-/

namespace Zlib.Trees.Proofs.Out
open Zlib.Trees

/-- The transmitted three-bit lengths in the actual fixed permutation. -/
def blLensBits (t : Nat → UInt16 × UInt16) (n : Nat) : List Bool :=
  (List.range n).flatMap fun r => natBits (t bl_order[r]!.toNat).2.toNat 3

/-- The three count fields, transmitted BL lengths and two source trees. -/
def allTreesBits (t : Nat → UInt16 × UInt16) (L D : Nat → Nat) (lc dc bc : Nat) : List Bool :=
  natBits (lc - 257) 5 ++ natBits (dc - 1) 5 ++ natBits (bc - 4) 4 ++
    blLensBits t bc ++ sendTreeBits t L (lc - 1) ++ sendTreeBits t D (dc - 1)

theorem blLensBits_succ (t : Nat → UInt16 × UInt16) (n : Nat) :
    blLensBits t (n + 1) = blLensBits t n ++ natBits (t bl_order[n]!.toNat).2.toNat 3 := by
  simp [blLensBits, List.range_succ, List.flatMap_append]

theorem blLensBits_length (t : Nat → UInt16 × UInt16) (n : Nat) :
    (blLensBits t n).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blLensBits_succ, List.length_append, ih]
    simp only [natBits, List.length_map, List.length_range]
    omega

theorem allTreesBits_length (t : Nat → UInt16 × UInt16) (L D : Nat → Nat) (lc dc bc : Nat) :
    (allTreesBits t L D lc dc bc).length = 14 + 3 * bc +
      (sendTreeBits t L (lc - 1)).length + (sendTreeBits t D (dc - 1)).length := by
  simp only [allTreesBits, List.length_append, blLensBits_length, natBits,
    List.length_map, List.length_range]

end Zlib.Trees.Proofs.Out
