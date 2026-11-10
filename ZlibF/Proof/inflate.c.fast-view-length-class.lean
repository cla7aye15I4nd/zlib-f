import ZlibF.Proof.«inflate.c.fast-view-dolen-len-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The checked length-table shape classifies every root entry into
the source's literal, length-base, second-level and terminal branches. -/
theorem len_table_root_cases
    {codes : Array Code} {baseOff rootBits index : Nat}
    (safe : LenTableSafe codes baseOff rootBits)
    (rootIndex : index < 2 ^ rootBits) :
    let offset := baseOff + index
    let entry := codes.getD offset default
    offset < codes.size ∧ entry.bits.toNat ≤ 15 ∧
      (entry.op = 0 ∨
       (entry.op &&& 16 ≠ 0 ∧
         (entry.op &&& 15).toNat ≤ 5 ∧
         3 ≤ entry.val.toNat ∧
         entry.val.toNat + 2 ^ (entry.op &&& 15).toNat ≤ 259) ∨
       (entry.op ≠ 0 ∧ entry.op &&& 16 = 0 ∧
         entry.op &&& 64 = 0 ∧
         1 ≤ entry.op.toNat ∧ entry.op.toNat ≤ 15 ∧
         baseOff + entry.val.toNat + 2 ^ entry.op.toNat ≤
           codes.size) ∨
       (entry.op &&& 16 = 0 ∧ entry.op &&& 64 ≠ 0)) := by
  rcases safe with ⟨_, rootSize, entries⟩
  have atBound : baseOff + index < codes.size := by
    omega
  have classified := entries index rootIndex
  let entry : Code := codes.getD (baseOff + index) default
  have classified' :
      (if LenLink entry then LinkOK LenLeaf codes baseOff entry
       else LenLeaf 0 entry) := by
    simpa only [entry] using classified
  by_cases isLink : LenLink entry
  · rw [if_pos isLink] at classified'
    rcases classified' with ⟨bits, opMin, opMax, bound, _⟩
    exact ⟨atBound, bits,
      Or.inr (Or.inr (Or.inl ⟨isLink.1, isLink.2.1,
        isLink.2.2, opMin, opMax, bound⟩))⟩
  · rw [if_neg isLink] at classified'
    rcases classified' with ⟨bits, literal | base | terminal⟩
    · exact ⟨atBound, bits, Or.inl literal⟩
    · exact ⟨atBound, bits, Or.inr (Or.inl base)⟩
    · exact ⟨atBound, bits,
        Or.inr (Or.inr (Or.inr terminal))⟩

/-- A selected second-level length entry remains inside the array and
is a leaf whose total code width fits the fifteen held bits. -/
theorem len_table_link_target
    {codes : Array Code} {baseOff rootBits rootIndex slice : Nat}
    (safe : LenTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
    (link : LenLink (codes.getD (baseOff + rootIndex) default))
    (sliceBound : slice <
      2 ^ (codes.getD (baseOff + rootIndex) default).op.toNat) :
    let entry := codes.getD (baseOff + rootIndex) default
    let target := baseOff + entry.val.toNat + slice
    target < codes.size ∧
      LenLeaf entry.bits.toNat (codes.getD target default) ∧
      (codes.getD target default).bits.toNat +
        entry.bits.toNat ≤ 15 := by
  rcases safe with ⟨_, _, entries⟩
  have selected := entries rootIndex root
  rw [if_pos link] at selected
  rcases selected with ⟨_, _, _, size, leaves⟩
  have bound : baseOff +
      (codes.getD (baseOff + rootIndex) default).val.toNat +
      slice < codes.size := by
    omega
  have leaf := leaves slice sliceBound
  exact ⟨bound, leaf, leaf.1⟩

end Zlib.Inflate.Proofs
