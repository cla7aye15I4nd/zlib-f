import ZlibF.Math.DeflateRankedLengths
import ZlibF.Math.DeflateHuffmanChain

/-! # The actual clamped first-pass histogram in leaf-rank form -/

namespace Zlib.Trees.Proofs.GB.LeafRank
set_option autoImplicit false

/-- Clamping the mathematical levels commutes with their source-order
construction. The bound 1000 is above every retained heap path. -/
theorem clK_min (H : Nat → Nat) (hm elems L : Nat) (bound : L ≤ 1000) :
    ∀ k v, clK H hm elems L k v = min (clK H hm elems 1000 k v) L
  | 0, v => by simp [clK]
  | k + 1, v => by
    simp only [clK]
    split
    · rw [clK_min H hm elems L bound k]; omega
    · exact clK_min H hm elems L bound k v

/-- The source first-pass leaf histogram is exactly histR of mathematical
levels indexed by the actual retained leaf ranks. -/
theorem capped_histogram (H : Nat → Nat) (hm J elems maxc : Nat) :
    Zlib.Trees.HuffmanAbstract.histR (value H (clK H hm elems 1000 (2 * J)) hm J maxc)
      (count H hm J maxc) = fun b => blC H hm J maxc (clK H hm elems 15 (2 * J)) b := by
  funext b
  unfold Zlib.Trees.HuffmanAbstract.histR count
  rw [countR_reindex]
  unfold blC
  apply rs_congr
  intro i bound
  by_cases leaf : H (hm + 1 + i) ≤ maxc
  · have same := idxR_rank (selected H hm maxc) bound (by simp only [selected, leaf, decide_true])
    simp only [value, index, selected, leaf, decide_true, true_and] at same ⊢
    rw [same, clK_min H hm elems 15 (by omega)]
    by_cases equal : min (clK H hm elems 1000 (2 * J) (H (hm + 1 + i))) 15 = b <;> simp [equal, leaf]
  · simp [selected, leaf]

/-- Finite leaf-rank count cannot exceed the retained position count. -/
theorem count_le (H : Nat → Nat) (hm J maxc : Nat) : count H hm J maxc ≤ 2 * J := by
  have bound := rs_le (n := 2 * J) (F := fun i => if selected H hm maxc i then 1 else 0)
    (G := fun _ => 1) (fun i _ => by split <;> omega)
  rw [rs_const] at bound
  simpa only [count, cntL, Nat.one_mul] using bound

/-- Every full binary retained tree has a leaf. In particular, the first
removed node at position 572 cannot be an internal node. -/
theorem count_positive {H : Nat → Nat} {hm J elems maxc : Nat} (shape : PShape H hm J elems maxc) :
    1 ≤ count H hm J maxc := by
  have boundary := shape.hm_eq
  have internal := shape.J1
  have leaf : H 572 ≤ maxc := by
    rcases shape.kind 572 (by omega) (by omega) with leaf | node
    · exact leaf
    · obtain ⟨q, lo, hi, value⟩ := shape.appears (H 572 - elems) (by omega)
      have same := shape.inj q 572 lo (by omega) (by omega) (by omega) (by rw [value]; omega)
      omega
  have position : hm + 1 + (2 * J - 1) = 572 := by omega
  have bounds := rank_bounds (selected H hm maxc) (n := 2 * J) (i := 2 * J - 1) (by omega)
    (by simp only [selected, position, leaf, decide_true])
  exact Nat.le_trans bounds.1 bounds.2

/-- The abstract weighted Kraft sum uses the same finite sum as the
source first-pass proof. -/
theorem krS_rs (c : Nat → Nat) : ∀ j,
    Zlib.Trees.HuffmanAbstract.wsum (fun i => 2 ^ (15 - i)) c j =
      rs (fun b => c b * 2 ^ (15 - b)) (j + 1)
  | 0 => by simp [Zlib.Trees.HuffmanAbstract.wsum, rs]
  | j + 1 => by rw [Zlib.Trees.HuffmanAbstract.wsum, krS_rs c j, rs_succ (n := j + 1)]

/-- The ancestor chain supplies the quantitative Fibonacci bound for each
actual retained non-root node, before any length-limiting repair. -/
theorem fib_bound {H : Nat → Nat} {hm J elems maxc : Nat} (shape : PShape H hm J elems maxc)
    (w : Nat → Nat)
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ w (H q)) :
    ∀ q, hm < q → q < 573 →
      w (H q) * Zlib.Trees.HuffmanAbstract.fib (clK H hm elems 1000 (2 * J) (H q) + 1) +
        Zlib.Trees.HuffmanAbstract.fib (clK H hm elems 1000 (2 * J) (H q)) ≤ w (H hm) := by
  intro q lower upper
  obtain ⟨p, s, initial, steps, first, siblings, last, _sibling⟩ := leaf_chain shape
    (clK_clamped (L := 1000) shape) w (w (H hm)) sums ordered positive rfl _ q lower upper rfl
  have bound := Zlib.Trees.HuffmanAbstract.fibChain_bound p s _ _ initial steps first siblings
  rw [last] at bound
  exact bound

end Zlib.Trees.Proofs.GB.LeafRank
