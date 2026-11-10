import ZlibF.Proof.«inflate.c.fast-view-dodist-link-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The checked distance-table shape classifies each root entry into the
three translated `dodist` branches with the required bounds. -/
theorem dist_table_root_cases
    {codes : Array Code} {baseOff rootBits index : Nat}
    (safe : DistTableSafe codes baseOff rootBits)
    (rootIndex : index < 2 ^ rootBits) :
    let offset := baseOff + index
    let entry := codes.getD offset default
    offset < codes.size ∧
      entry.bits.toNat ≤ 15 ∧
      ((entry.op &&& 16 ≠ 0 ∧
        (entry.op &&& 15).toNat ≤ 13 ∧
        1 ≤ entry.val.toNat) ∨
       (entry.op &&& 16 = 0 ∧
        entry.op &&& 64 = 0 ∧
        1 ≤ entry.op.toNat ∧
        entry.op.toNat ≤ 15 ∧
        baseOff + entry.val.toNat +
          2 ^ entry.op.toNat ≤ codes.size) ∨
       (entry.op &&& 16 = 0 ∧
        entry.op &&& 64 ≠ 0)) := by
  rcases safe with ⟨_, rootSize, entries⟩
  have atBound : baseOff + index < codes.size := by
    have span : index < 2 ^ rootBits := rootIndex
    omega
  have classified := entries index rootIndex
  let entry : Code := codes.getD (baseOff + index) default
  have classified' :
      (if DistLink entry then LinkOK DistLeaf codes baseOff entry
       else DistLeaf 0 entry) := by
    simpa only [entry] using classified
  by_cases isLink : DistLink entry
  · rw [if_pos isLink] at classified'
    rcases classified' with ⟨bits, opMin, opMax, bound, _⟩
    exact ⟨atBound, bits,
      Or.inr (Or.inl ⟨isLink.1, isLink.2,
        opMin, opMax, bound⟩)⟩
  · rw [if_neg isLink] at classified'
    rcases classified' with ⟨bits, base | invalid⟩
    · exact ⟨atBound, bits, Or.inl base⟩
    · exact ⟨atBound, bits, Or.inr (Or.inr invalid)⟩

/-- Every bounded second-level distance lookup reaches a leaf and consumes
at most fifteen bits together with its root link. -/
theorem dist_table_link_target
    {codes : Array Code} {baseOff rootBits rootIndex slice : Nat}
    (safe : DistTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
    (link : DistLink (codes.getD (baseOff + rootIndex) default))
    (sliceBound : slice <
      2 ^ (codes.getD (baseOff + rootIndex) default).op.toNat) :
    let entry := codes.getD (baseOff + rootIndex) default
    let target := baseOff + entry.val.toNat + slice
    target < codes.size ∧
      DistLeaf entry.bits.toNat (codes.getD target default) ∧
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
