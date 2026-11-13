import ZlibF.Proof.«trees.c.build.rank-cost»
import ZlibF.Proof.«deflate.c.engine.overlay-reference»

/-!
# trees.c: final lengths against any reference code, up to the repair cost (H1 + H2a)

On the heap tree, a rank-cost bound `Σ_r w·len ≤ Σ_r w·δ + E` (true depths `δ`) and H1
(`PShape.depth_cost_le_kraft`) give, over the used symbols `T` and for every reference code `ℓ`
with Kraft sum at most one on `T`,

`Σ_T w·len ≤ Σ_T w·ℓ + E`.

`BTRankOrigins.cost_le_kraft` states it for the tree `build_tree` returns, with `E` the
`repairExtra` of the length repair. This is the header bound of the TinyOverlay plan with Δ left
as `E`; bounding `E` is H2b.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

namespace GB

/-- A sum over leaf ranks is the sum over the leaf positions. -/
theorem LeafRank.rank_sum_eq (H F : Nat → Nat) (hm J maxc : Nat) :
    HuffmanAbstract.sumR (fun r => F (H (hm + 1 + LeafRank.index H hm J maxc r))) (LeafRank.count H hm J maxc) =
      rs (fun i => if H (hm + 1 + i) ≤ maxc then F (H (hm + 1 + i)) else 0) (2 * J) := by
  unfold LeafRank.count
  rw [← sum_reindex (LeafRank.selected H hm maxc)]
  apply rs_congr
  intro i bound
  by_cases leaf : H (hm + 1 + i) ≤ maxc
  · have same := idxR_rank (LeafRank.selected H hm maxc) bound
      (by simp only [LeafRank.selected, leaf, decide_true])
    have sel : LeafRank.selected H hm maxc i = true := by simp only [LeafRank.selected, leaf, decide_true]
    rw [ite_eq_left sel, ite_eq_left leaf]
    unfold LeafRank.index
    rw [same]
  · have sel : LeafRank.selected H hm maxc i = false := by simp only [LeafRank.selected, leaf, decide_false]
    rw [sel, ite_eq_right leaf]
    rfl

section
variable {H : Nat → Nat} {hm J elems maxc : Nat}

/-- **H1 + H2a on the heap tree.** -/
theorem PShape.cost_le_kraft (S : PShape H hm J elems maxc) (w len : Nat → Nat) (E : Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (cost : HuffmanAbstract.sumR (fun r => LeafRank.value H w hm J maxc r * LeafRank.value H len hm J maxc r)
        (LeafRank.count H hm J maxc) ≤
      HuffmanAbstract.sumR (fun r => LeafRank.value H w hm J maxc r *
        LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc r) (LeafRank.count H hm J maxc) + E)
    (T : Nat → Prop) [DecidablePred T] (hT : ∀ v ≤ maxc, T v ↔ ∃ q, hm < q ∧ q < 573 ∧ H q = v)
    (K : Nat) (ℓ : Nat → Nat) (bound : ∀ v ≤ maxc, T v → ℓ v ≤ K)
    (kraft : rs (fun v => if T v then 2 ^ (K - ℓ v) else 0) (maxc + 1) ≤ 2 ^ K) :
    rs (fun v => if T v then w v * len v else 0) (maxc + 1) ≤
      rs (fun v => if T v then w v * ℓ v else 0) (maxc + 1) + E := by
  have h1 := S.depth_cost_le_kraft (clK_clamped (L := 1000) S) w sums ordered T hT K ℓ bound kraft
  have eL := (LeafRank.rank_sum_eq H (fun v => w v * len v) hm J maxc).trans
    (S.leaf_sum T hT (fun v => w v * len v))
  have eD := (LeafRank.rank_sum_eq H (fun v => w v * clK H hm elems 1000 (2 * J) v) hm J maxc).trans
    (S.leaf_sum T hT (fun v => w v * clK H hm elems 1000 (2 * J) v))
  have cL : HuffmanAbstract.sumR (fun r => LeafRank.value H w hm J maxc r * LeafRank.value H len hm J maxc r)
      (LeafRank.count H hm J maxc) =
      HuffmanAbstract.sumR (fun r => (fun v => w v * len v) (H (hm + 1 + LeafRank.index H hm J maxc r)))
        (LeafRank.count H hm J maxc) := rfl
  have cD : HuffmanAbstract.sumR (fun r => LeafRank.value H w hm J maxc r *
        LeafRank.value H (clK H hm elems 1000 (2 * J)) hm J maxc r) (LeafRank.count H hm J maxc) =
      HuffmanAbstract.sumR (fun r => (fun v => w v * clK H hm elems 1000 (2 * J) v)
        (H (hm + 1 + LeafRank.index H hm J maxc r))) (LeafRank.count H hm J maxc) := rfl
  rw [cL, eL] at cost
  rw [cD, eD] at cost
  omega

end

end GB

/-- **H1 + H2a for the tree `build_tree` returns.** The used symbols `T` of the heap tree, with
the weights the tree was built from, cost at most their cost under any reference code of Kraft
sum at most one, plus the repair term. -/
theorem BTRankOrigins.cost_le_kraft {tk : TK} {N L : Nat} {original result : DeflateState}
    (origins : BTRankOrigins tk N L original result) :
    ∃ (prepared built : DeflateState) (mc : Int32) (K M : Nat),
      BTBuilt tk N K mc prepared built ∧
      ovP (Hn built) (574 - 2 * K) N L (clK (Hn built) (574 - 2 * K) N L (2 * (K - 1))) (2 * (K - 1)) = 2 * M ∧
      ∀ (T : Nat → Prop) [DecidablePred T],
        (∀ v ≤ mc.toInt.toNat, T v ↔ ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) →
        ∀ (B : Nat) (ℓ : Nat → Nat), (∀ v ≤ mc.toInt.toNat, T v → ℓ v ≤ B) →
          rs (fun v => if T v then 2 ^ (B - ℓ v) else 0) (mc.toInt.toNat + 1) ≤ 2 ^ B →
          rs (fun v => if T v then frn (tk.arr built) v * curL (tk.arr result) v else 0) (mc.toInt.toNat + 1) ≤
            rs (fun v => if T v then frn (tk.arr built) v * ℓ v else 0) (mc.toInt.toNat + 1) +
              HuffmanAbstract.repairExtra L
                (LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat) M
                (HuffmanAbstract.histL L
                  (LeafRank.value (Hn built) (clK (Hn built) (574 - 2 * K) N 1000 (2 * (K - 1)))
                    (574 - 2 * K) (K - 1) mc.toInt.toNat)
                  (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat)) := by
  obtain ⟨prepared, built, mc, K, tree, _weight, _frequencies, _used, sums, ordered, _positive, M, hM, cost⟩ :=
    origins
  refine ⟨prepared, built, mc, K, M, tree, hM, ?_⟩
  intro T _ hT B ℓ bound kraft
  exact tree.shape.cost_le_kraft (frn (tk.arr built)) (curL (tk.arr result)) _ sums ordered cost
    T hT B ℓ bound kraft

end Zlib.Trees.Proofs
