import ZlibF.Proof.«inflate.c.fast-view-dolen-root-terminals-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A safe literal/length leaf falls into exactly one of the source's
literal, base, block-end or invalid-code tests. -/
theorem len_leaf_source_cases {d : Nat} {entry : Code}
    (leaf : LenLeaf d entry) :
    entry.bits.toNat ≤ 15 ∧
      (entry.op = 0 ∨
       (entry.op &&& 16 ≠ 0 ∧
         (entry.op &&& 15).toNat ≤ 5 ∧
         3 ≤ entry.val.toNat ∧
         entry.val.toNat +
           2 ^ (entry.op &&& 15).toNat ≤ 259) ∨
       (entry.op ≠ 0 ∧
         (entry.op.toUInt32 &&& 16 != 0) = false ∧
         (entry.op.toUInt32 &&& 64 == 0) = false ∧
         (entry.op.toUInt32 &&& 32 != 0) = true) ∨
       (entry.op ≠ 0 ∧
         (entry.op.toUInt32 &&& 16 != 0) = false ∧
         (entry.op.toUInt32 &&& 64 == 0) = false ∧
         (entry.op.toUInt32 &&& 32 != 0) = false)) := by
  have width : entry.bits.toNat ≤ 15 := by
    have total := leaf.1
    omega
  refine ⟨width, ?_⟩
  rcases leaf.2 with literal | base | terminal
  · exact Or.inl literal
  · exact Or.inr (Or.inl base)
  · have nonzero : entry.op ≠ 0 := by
      intro zero
      rw [zero] at terminal
      simp at terminal
    have notBase :
        (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [terminal.1]
    have notLink :
        (entry.op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [terminal.2]
    by_cases endCode : entry.op &&& 32 = 0
    · have notEnd :
          (entry.op.toUInt32 &&& 32 != 0) = false := by
        rw [Zlib.Inffast.Proofs.mask32]
        simp [endCode]
      exact Or.inr (Or.inr (Or.inr
        ⟨nonzero, notBase, notLink, notEnd⟩))
    · have isEnd :
          (entry.op.toUInt32 &&& 32 != 0) = true := by
        rw [Zlib.Inffast.Proofs.mask32]
        simp [endCode]
      exact Or.inr (Or.inr (Or.inl
        ⟨nonzero, notBase, notLink, isEnd⟩))

/-- The checked root table selects either one bounded link or a leaf
that falls into one of the four translated source branches. -/
theorem len_table_root_source_cases
    {codes : Array Code} {baseOff rootBits rootIndex : Nat}
    (safe : LenTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits) :
    let entry := codes.getD (baseOff + rootIndex) default
    baseOff + rootIndex < codes.size ∧
      ((LenLink entry ∧ LinkOK LenLeaf codes baseOff entry) ∨
       (¬ LenLink entry ∧ entry.bits.toNat ≤ 15 ∧
        (entry.op = 0 ∨
         (entry.op &&& 16 ≠ 0 ∧
           (entry.op &&& 15).toNat ≤ 5 ∧
           3 ≤ entry.val.toNat ∧
           entry.val.toNat +
             2 ^ (entry.op &&& 15).toNat ≤ 259) ∨
         (entry.op ≠ 0 ∧
           (entry.op.toUInt32 &&& 16 != 0) = false ∧
           (entry.op.toUInt32 &&& 64 == 0) = false ∧
           (entry.op.toUInt32 &&& 32 != 0) = true) ∨
         (entry.op ≠ 0 ∧
           (entry.op.toUInt32 &&& 16 != 0) = false ∧
           (entry.op.toUInt32 &&& 64 == 0) = false ∧
           (entry.op.toUInt32 &&& 32 != 0) = false)))) := by
  have bound : baseOff + rootIndex < codes.size := by
    rcases safe with ⟨_, extent, _⟩
    omega
  have selected := safe.2.2 rootIndex root
  by_cases link : LenLink
      (codes.getD (baseOff + rootIndex) default)
  · rw [if_pos link] at selected
    exact ⟨bound, Or.inl ⟨link, selected⟩⟩
  · rw [if_neg link] at selected
    have classified := len_leaf_source_cases selected
    exact ⟨bound, Or.inr ⟨link, classified⟩⟩

/-- The selected second-level entry is bounded and falls into one of
the same four source branches. -/
theorem len_table_link_source_cases
    {codes : Array Code} {baseOff rootBits rootIndex slice : Nat}
    (safe : LenTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
    (link : LenLink (codes.getD (baseOff + rootIndex) default))
    (sliceBound : slice <
      2 ^ (codes.getD (baseOff + rootIndex) default).op.toNat) :
    let rootEntry := codes.getD (baseOff + rootIndex) default
    let targetIndex := baseOff + rootEntry.val.toNat + slice
    let target := codes.getD targetIndex default
    targetIndex < codes.size ∧
      LenLeaf rootEntry.bits.toNat target ∧
      (target.op = 0 ∨
       (target.op &&& 16 ≠ 0 ∧
         (target.op &&& 15).toNat ≤ 5 ∧
         3 ≤ target.val.toNat ∧
         target.val.toNat +
           2 ^ (target.op &&& 15).toNat ≤ 259) ∨
       (target.op ≠ 0 ∧
         (target.op.toUInt32 &&& 16 != 0) = false ∧
         (target.op.toUInt32 &&& 64 == 0) = false ∧
         (target.op.toUInt32 &&& 32 != 0) = true) ∨
       (target.op ≠ 0 ∧
         (target.op.toUInt32 &&& 16 != 0) = false ∧
         (target.op.toUInt32 &&& 64 == 0) = false ∧
         (target.op.toUInt32 &&& 32 != 0) = false)) := by
  obtain ⟨bound, leaf, _⟩ :=
    len_table_link_target safe root link sliceBound
  exact ⟨bound, leaf, (len_leaf_source_cases leaf).2⟩

/-- The translated first-pass execution fixes the selected link slice:
two descriptions of the same returned pointer use the same offset. -/
theorem dolen_link_slice_unique
    {h : Heap} {c : Zlib.Inffast.Ctx}
    {l linked₁ linked₂ : Zlib.Inffast.L}
    {codeRef : CodeRef} {baseOff value slice₁ slice₂ : Nat}
    (run₁ : C.run (Zlib.Inffast.dolen c l) h =
      .ok (linked₁, h))
    (run₂ : C.run (Zlib.Inffast.dolen c l) h =
      .ok (linked₂, h))
    (here₁ : linked₁.here = .ref codeRef
      (baseOff + value + slice₁))
    (here₂ : linked₂.here = .ref codeRef
      (baseOff + value + slice₂)) :
    linked₁ = linked₂ ∧ slice₁ = slice₂ := by
  rw [run₁] at run₂
  cases run₂
  have same : baseOff + value + slice₁ =
      baseOff + value + slice₂ := by
    have equal : (Ptr.ref codeRef
        (baseOff + value + slice₁) : CodePtr) =
        .ref codeRef (baseOff + value + slice₂) := by
      exact here₁.symm.trans here₂
    exact (Ptr.ref.inj equal).2
  exact ⟨rfl, by omega⟩

end Zlib.Inflate.Proofs
