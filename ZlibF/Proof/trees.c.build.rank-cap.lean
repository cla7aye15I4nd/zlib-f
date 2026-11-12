import ZlibF.Proof.«trees.c.build.rank-reference»
import ZlibF.Math.HuffmanRepairCap
import ZlibF.Math.RepairCap13
import ZlibF.Math.RepairCap15

/-!
# trees.c: the repair term of the 7-bit tree under Fibonacci caps (H2b)

On a heap tree of weight `W ≤ 316` whose first pass overflows at the limit 7, the clamped histogram
has the shape `RepairShape` (`kraft_clamped`, `blC_top`, `exactC_pos`), and every leaf rank obeys
its Fibonacci cap (`LeafRank.fib_bound`, `rank_cap`). The generated case analyses
(`repairExtra_cap13`, `repairExtra_cap15`) then bound the repair term:

* at most 13 leaves: `repairExtra ≤ 29 + W / 2`;
* at most 15 leaves: `repairExtra ≤ 245`.

`BTRankOrigins.cost_le_kraft_cap13` / `_cap15` combine this with H1 and H2a for the tree that
`build_tree` returns at the limit 7.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

namespace GB
section
variable {H : Nat → Nat} {hm J elems maxc : Nat}

/-- The clamped histogram at the limit 7 of an overflowing heap tree has `RepairShape`. -/
theorem PShape.repairShape (S : PShape H hm J elems maxc) {M : Nat}
    (hM : ovP H hm elems 7 (clK H hm elems 7 (2 * J)) (2 * J) = 2 * M) (pos : 1 ≤ M) :
    HuffmanAbstract.RepairShape
      (HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
        (LeafRank.count H hm J maxc))
      (LeafRank.count H hm J maxc) M := by
  have hm_eq := S.hm_eq
  have C := clK_clamped (L := 7) S
  have C1000 := clK_clamped (L := 1000) S
  have capped := capped_histogram_le H hm J elems maxc 7 (by omega)
  have depth : ∀ r, 1 ≤ r → r ≤ LeafRank.count H hm J maxc →
      1 ≤ LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc r := by
    intro r lower upper
    have spec := LeafRank.index_spec lower upper
    unfold LeafRank.value
    rw [C1000.step _ spec.1]
    omega
  have zero : HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
      (LeafRank.count H hm J maxc) 0 = 0 :=
    HuffmanAbstract.countR_none _ _ fun r a b => by have := depth r a b; simp; omega
  have kraft := kraft_clamped S C (by omega)
  rw [kraftC_eq S C] at kraft
  have ov : ovfC H hm J elems 7 (clK H hm elems 7 (2 * J)) = 2 * M := hM
  rw [ov] at kraft
  have top := (blC_top S C (by omega)).2
  rw [ov] at top
  have exact : 0 < exactC H hm J elems 7 (clK H hm elems 7 (2 * J)) :=
    exactC_pos S C (by omega) (by rw [ov]; omega)
  have e : ∀ b, HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
      (LeafRank.count H hm J maxc) b = blC H hm J maxc (clK H hm elems 7 (2 * J)) b :=
    fun b => congrFun capped b
  have z0 := zero
  rw [e 0] at z0
  have expand : rs (fun b => blC H hm J maxc (clK H hm elems 7 (2 * J)) b * 2 ^ (7 - b)) (7 + 1) =
      blC H hm J maxc (clK H hm elems 7 (2 * J)) 0 * 128 + blC H hm J maxc (clK H hm elems 7 (2 * J)) 1 * 64 +
      blC H hm J maxc (clK H hm elems 7 (2 * J)) 2 * 32 + blC H hm J maxc (clK H hm elems 7 (2 * J)) 3 * 16 +
      blC H hm J maxc (clK H hm elems 7 (2 * J)) 4 * 8 + blC H hm J maxc (clK H hm elems 7 (2 * J)) 5 * 4 +
      blC H hm J maxc (clK H hm elems 7 (2 * J)) 6 * 2 + blC H hm J maxc (clK H hm elems 7 (2 * J)) 7 * 1 := by
    simp only [rs_succ, rs_zero, Nat.zero_add]
  have p8 : (2 : Nat) ^ (7 + 1) = 256 := rfl
  rw [expand, p8] at kraft
  refine ⟨zero, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact HuffmanAbstract.countR_none _ _ fun r _ _ => by simp; omega
  · have all : HuffmanAbstract.cumC (HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
        (LeafRank.count H hm J maxc)) 7 = LeafRank.count H hm J maxc := by
      unfold HuffmanAbstract.histL
      rw [HuffmanAbstract.cumC_hist]
      exact HuffmanAbstract.countR_all _ _ fun r _ _ => by simp; omega
    simp only [HuffmanAbstract.cumC] at all
    rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7] at all
    rw [e 1, e 2, e 3, e 4, e 5, e 6, e 7]
    omega
  · rw [e 1, e 2, e 3, e 4, e 5, e 6, e 7]
    omega
  · rw [e 7]
    omega

end

end GB

namespace GB
section
variable {H : Nat → Nat} {hm J elems maxc : Nat}

/-- **The repair term under the caps, 13 leaves.** -/
theorem PShape.repairExtra_cap13 (S : PShape H hm J elems maxc) (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ w (H q)) {M : Nat}
    (hM : ovP H hm elems 7 (clK H hm elems 7 (2 * J)) (2 * J) = 2 * M)
    (leaves : LeafRank.count H hm J maxc ≤ 13) (weight : w (H hm) ≤ 316) :
    HuffmanAbstract.repairExtra 7 (LeafRank.value H w hm J maxc) M
      (HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
        (LeafRank.count H hm J maxc)) ≤ 29 + w (H hm) / 2 := by
  have hm_eq := S.hm_eq
  rcases Nat.eq_zero_or_pos M with m | m
  · subst m; simp [HuffmanAbstract.repairExtra]
  have hw := weights_antitone (H := H) (w := w) (hm := hm) (J := J) (maxc := maxc) ordered (by omega)
  have chain := LeafRank.fib_bound S w sums ordered positive
  have caps := HuffmanAbstract.rank_cap 7 (LeafRank.count H hm J maxc) (w (H hm))
    (LeafRank.value H w hm J maxc) (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc) hw
    (fun y lower upper => by
      have spec := LeafRank.index_spec lower upper
      exact chain _ (by omega) (by omega))
  exact HuffmanAbstract.repairExtra_cap13 _ _ _ _ M (S.repairShape hM m) leaves m caps weight

/-- **The repair term under the caps, 15 leaves.** -/
theorem PShape.repairExtra_cap15 (S : PShape H hm J elems maxc) (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ w (H q)) {M : Nat}
    (hM : ovP H hm elems 7 (clK H hm elems 7 (2 * J)) (2 * J) = 2 * M)
    (leaves : LeafRank.count H hm J maxc ≤ 15) (weight : w (H hm) ≤ 316) :
    HuffmanAbstract.repairExtra 7 (LeafRank.value H w hm J maxc) M
      (HuffmanAbstract.histL 7 (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc)
        (LeafRank.count H hm J maxc)) ≤ 245 := by
  have hm_eq := S.hm_eq
  rcases Nat.eq_zero_or_pos M with m | m
  · subst m; simp [HuffmanAbstract.repairExtra]
  have hw := weights_antitone (H := H) (w := w) (hm := hm) (J := J) (maxc := maxc) ordered (by omega)
  have chain := LeafRank.fib_bound S w sums ordered positive
  have caps := HuffmanAbstract.rank_cap 7 (LeafRank.count H hm J maxc) (w (H hm))
    (LeafRank.value H w hm J maxc) (LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc) hw
    (fun y lower upper => by
      have spec := LeafRank.index_spec lower upper
      exact chain _ (by omega) (by omega))
  exact HuffmanAbstract.repairExtra_cap15 _ _ _ _ M (S.repairShape hM m) leaves m caps weight

end
end GB

/-- **H1 + H2a + H2b for the 7-bit tree, at most 13 leaves.** Over the leaves `T` of the tree
`build_tree` returns, with the built weights and the root weight `W ≤ 316`:
`Σ_T w·len ≤ Σ_T w·ℓ + 29 + W / 2` for every reference `ℓ` of Kraft sum at most one. -/
theorem BTRankOrigins.cost_le_kraft_cap13 {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTRankOrigins tk N 7 original result) :
    ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
      BTBuilt tk N K mc prepared built ∧
      (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat ≤ 13 →
        frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ 316 →
        ∀ (T : Nat → Prop) [DecidablePred T],
          (∀ v ≤ mc.toInt.toNat, T v ↔ ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) →
          ∀ (B : Nat) (ℓ : Nat → Nat), (∀ v ≤ mc.toInt.toNat, T v → ℓ v ≤ B) →
            rs (fun v => if T v then 2 ^ (B - ℓ v) else 0) (mc.toInt.toNat + 1) ≤ 2 ^ B →
            rs (fun v => if T v then frn (tk.arr built) v * curL (tk.arr result) v else 0) (mc.toInt.toNat + 1) ≤
              rs (fun v => if T v then frn (tk.arr built) v * ℓ v else 0) (mc.toInt.toNat + 1) +
                (29 + frn (tk.arr built) (Hn built (574 - 2 * K)) / 2)) := by
  obtain ⟨prepared, built, mc, K, tree, _weight, _frequencies, _used, sums, ordered, positive, M, hM, cost⟩ :=
    origins
  refine ⟨prepared, built, mc, K, tree, ?_⟩
  intro leaves weight T _ hT B ℓ bound kraft
  have main := tree.shape.cost_le_kraft (frn (tk.arr built)) (curL (tk.arr result)) _ sums ordered cost
    T hT B ℓ bound kraft
  have cap := tree.shape.repairExtra_cap13 (frn (tk.arr built)) sums ordered
    (fun q lo hi => positive q (by omega) hi) hM leaves weight
  omega

/-- **H1 + H2a + H2b for the 7-bit tree, at most 15 leaves.** -/
theorem BTRankOrigins.cost_le_kraft_cap15 {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTRankOrigins tk N 7 original result) :
    ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
      BTBuilt tk N K mc prepared built ∧
      (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat ≤ 15 →
        frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ 316 →
        ∀ (T : Nat → Prop) [DecidablePred T],
          (∀ v ≤ mc.toInt.toNat, T v ↔ ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) →
          ∀ (B : Nat) (ℓ : Nat → Nat), (∀ v ≤ mc.toInt.toNat, T v → ℓ v ≤ B) →
            rs (fun v => if T v then 2 ^ (B - ℓ v) else 0) (mc.toInt.toNat + 1) ≤ 2 ^ B →
            rs (fun v => if T v then frn (tk.arr built) v * curL (tk.arr result) v else 0) (mc.toInt.toNat + 1) ≤
              rs (fun v => if T v then frn (tk.arr built) v * ℓ v else 0) (mc.toInt.toNat + 1) + 245) := by
  obtain ⟨prepared, built, mc, K, tree, _weight, _frequencies, _used, sums, ordered, positive, M, hM, cost⟩ :=
    origins
  refine ⟨prepared, built, mc, K, tree, ?_⟩
  intro leaves weight T _ hT B ℓ bound kraft
  have main := tree.shape.cost_le_kraft (frn (tk.arr built)) (curL (tk.arr result)) _ sums ordered cost
    T hT B ℓ bound kraft
  have cap := tree.shape.repairExtra_cap15 (frn (tk.arr built)) sums ordered
    (fun q lo hi => positive q (by omega) hi) hM leaves weight
  omega

end Zlib.Trees.Proofs
