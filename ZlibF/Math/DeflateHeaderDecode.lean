import ZlibF.Math.DeflateHeader
import ZlibF.Math.DeflateRunDecode

/-! # Reading the dynamic header's scalar fields and length permutation -/

namespace Zlib.Trees.Proofs.Out
open ZlibF.Spec Zlib.Trees

/-- The actual permutation is the independent format permutation. Its
inverse stays in range and names the original symbol. -/
theorem clOrder_index (i : Nat) (hi : i < 19) :
    clOrder.idxOf i < 19 ∧ bl_order[clOrder.idxOf i]!.toNat = i := by
  have ht : ∀ i : Fin 19,
      clOrder.idxOf i.val < 19 ∧ bl_order[clOrder.idxOf i.val]!.toNat = i.val := by decide +kernel
  exact ht ⟨i, hi⟩

/-- A list of bounded low-bit fields is read exactly, retaining its suffix. -/
theorem readNats_natBits (width : Nat) (vs : List Nat) (suffix : List Bool)
    (hf : ∀ v ∈ vs, v < 2 ^ width) :
    readNats width vs.length (vs.flatMap (fun v => natBits v width) ++ suffix) = some (vs, suffix) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readNats]
    rw [readBits_natBits width v _ (hf v (by simp))]
    simp only
    rw [ih (fun v hv => hf v (by simp [hv]))]

/-- Reading the transmitted three-bit values recovers their rank order. -/
theorem readNats_blLensBits (t : Nat → UInt16 × UInt16) (B : Nat) (suffix : List Bool)
    (hB : B ≤ 19) (h7 : ∀ k < 19, (t k).2.toNat ≤ 7) :
    readNats 3 B (blLensBits t B ++ suffix) =
      some ((List.range B).map (fun r => (t bl_order[r]!.toNat).2.toNat), suffix) := by
  have ht := readNats_natBits 3 ((List.range B).map (fun r => (t bl_order[r]!.toNat).2.toNat)) suffix
    (by
      intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      have hri : r < 19 := by have := List.mem_range.mp hr; omega
      have hb : bl_order[r]!.toNat < 19 := by
        have ht : ∀ i : Fin 19, bl_order[i.val]!.toNat < 19 := by decide +kernel
        exact ht ⟨r, hri⟩
      have := h7 _ hb
      omega)
  simpa only [List.length_map, List.length_range, List.flatMap_map, blLensBits] using ht

/-- The independent reader restores all nineteen lengths in symbol order.
Omitted ranks must have zero length; that premise is a constructor fact. -/
theorem readCodeLenLens_blLensBits (t : Nat → UInt16 × UInt16) (B : Nat) (suffix : List Bool)
    (hB : B ≤ 19) (h7 : ∀ k < 19, (t k).2.toNat ≤ 7)
    (hz : ∀ rank, B ≤ rank → rank < 19 → (t bl_order[rank]!.toNat).2.toNat = 0) :
    readCodeLenLens B (blLensBits t B ++ suffix) =
      some (lens (fun i => (t i).2.toNat) 19, suffix) := by
  unfold readCodeLenLens
  rw [readNats_blLensBits t B suffix hB h7]
  dsimp only
  congr 2
  apply List.map_congr_left
  intro i hi
  have hir : i < 19 := List.mem_range.mp hi
  obtain ⟨hr, he⟩ := clOrder_index i hir
  by_cases hb : clOrder.idxOf i < B
  · rw [ite_eq_left hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hb, Option.map_some, Option.getD_some, he]
  · rw [ite_eq_right hb]
    have hv := hz (clOrder.idxOf i) (by omega) hr
    rw [he] at hv
    exact hv.symm

/-- The independent readers recover all scalar fields and the complete BL
length list, leaving exactly the two encoded source trees and the suffix. -/
theorem allTreesBits_read_fields (t : Nat → UInt16 × UInt16) (L D : Nat → Nat)
    (lc dc bc : Nat) (suffix : List Bool)
    (hl0 : 257 ≤ lc) (hl1 : lc ≤ 286) (hd0 : 1 ≤ dc) (hd1 : dc ≤ 30)
    (hb0 : 4 ≤ bc) (hb1 : bc ≤ 19)
    (h7 : ∀ k < 19, (t k).2.toNat ≤ 7)
    (hz : ∀ rank, bc ≤ rank → rank < 19 → (t bl_order[rank]!.toNat).2.toNat = 0) :
    (do
      let (hlit, r1) ← readBits 5 (allTreesBits t L D lc dc bc ++ suffix)
      let (hdist, r2) ← readBits 5 r1
      let (hclen, r3) ← readBits 4 r2
      let (cl, r4) ← readCodeLenLens (hclen + 4) r3
      pure (hlit, hdist, hclen, cl, r4)) =
      some (lc - 257, dc - 1, bc - 4, lens (fun i => (t i).2.toNat) 19,
        sendTreeBits t L (lc - 1) ++ sendTreeBits t D (dc - 1) ++ suffix) := by
  simp only [allTreesBits, List.append_assoc]
  rw [readBits_natBits 5 _ _ (by omega)]
  dsimp only [bind, Option.bind]
  rw [readBits_natBits 5 _ _ (by omega)]
  dsimp only
  rw [readBits_natBits 4 _ _ (by omega)]
  dsimp only
  rw [show bc - 4 + 4 = bc by omega, readCodeLenLens_blLensBits t bc _ hb1 h7 hz]
  rfl

/-- A larger length list consists of its used prefix and trailing zeros. -/
theorem lens_trailing_zeros (L : Nat → Nat) (n m : Nat) (hn : n ≤ m)
    (hz : ∀ i, n ≤ i → i < m → L i = 0) :
    lens L m = lens L n ++ List.replicate (m - n) 0 := by
  have ht := lens_add_rep L n (m - n) 0 (fun i hi1 hi2 => hz i hi1 (by omega))
  simpa only [Nat.add_sub_cancel' hn] using ht

end Zlib.Trees.Proofs.Out
