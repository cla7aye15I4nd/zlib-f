import ZlibF.Proof.«trees.c.heap.gbtree»

/-! # Queue and descending tail as one finite sequence of tree nodes -/

namespace Zlib.Trees.Proofs.GB

/-- Enumerate the active queue, then the descending tail. -/
def poolAt (H : Nat → Nat) (len i : Nat) : Nat :=
  if i < len then H (i + 1) else H (572 - (i - len))

/-- Observe all active queue entries and all retained tail entries. -/
def poolSum (H : Nat → Nat) (len tail : Nat) (F : Nat → Nat) : Nat :=
  rs (fun i => F (H (i + 1))) len + rs (fun i => F (H (572 - i))) tail

/-- The two sums are exactly one bounded sequence sum. -/
theorem poolSum_eq_rs (H : Nat → Nat) (len tail : Nat) (F : Nat → Nat) :
    poolSum H len tail F = rs (fun i => F (poolAt H len i)) (len + tail) := by
  rw [rs_split]
  unfold poolSum
  congr 1
  · apply rs_congr
    intro i hi
    simp only [poolAt, hi, ite_true]
  · apply rs_congr
    intro i hi
    simp only [poolAt, show ¬ len + i < len by omega, ite_false, Nat.add_sub_cancel_left]

/-- Two distinct summands fit inside the whole sum. -/
theorem two_le_rs (F : Nat → Nat) (m i j : Nat) (hi : i < m) (hj : j < m) (hne : i ≠ j) :
    F i + F j ≤ rs F m := by
  let G := fun q => if q = i then 0 else F q
  have hu := rs_upd (F := F) (G := G) (n := m) (k := i) hi (by
    intro q hq hqi
    dsimp only [G]
    rw [if_neg hqi])
  have hjG := le_rs (F := G) hj
  have hGi : G i = 0 := by simp only [G, ite_true]
  have hGj : G j = F j := by simp only [G, if_neg (Ne.symm hne)]
  rw [hGi] at hu
  rw [hGj] at hjG
  omega

/-- At most one occurrence of every value implies distinct entries. -/
theorem injective_of_counts (P : Nat → Nat) (m : Nat) (hc : ∀ v, cnt P m v ≤ 1) :
    ∀ i j, i < m → j < m → P i = P j → i = j := by
  intro i j hi hj heq
  by_cases hne : i = j
  · exact hne
  exfalso
  have htwo := two_le_rs (fun q => if P q = P i then 1 else 0) m i j hi hj hne
  have hcnt := hc (P i)
  have hji := heq.symm
  simp only [hji, ite_true] at htwo
  unfold cnt at hcnt
  omega

/-- The queue/tail index map hits only active heap positions. -/
theorem poolAt_position (H : Nat → Nat) (K j i : Nat) (hK : K ≤ 286) (hj : j < K) (hi : i < K + j) :
    ∃ q : Nat, ((1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) ∧ poolAt H (K - j) i = H q := by
  by_cases hq : i < K - j
  · exact ⟨i + 1, Or.inl ⟨by omega, by omega⟩, by simp only [poolAt, hq, ite_true]⟩
  · refine ⟨572 - (i - (K - j)), Or.inr ⟨by omega, by omega⟩, ?_⟩
    simp only [poolAt, hq, ite_false]

/-- Every active heap position has a bounded queue/tail sequence index. -/
theorem poolAt_preimage (H : Nat → Nat) (K j q : Nat) (hK : K ≤ 286) (hj : j < K)
    (hq : (1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) :
    ∃ i : Nat, i < K + j ∧ poolAt H (K - j) i = H q := by
  rcases hq with hq | hq
  · refine ⟨q - 1, by omega, ?_⟩
    simp only [poolAt, show q - 1 < K - j by omega, ite_true, show q - 1 + 1 = q by omega]
  · refine ⟨K - j + (572 - q), by omega, ?_⟩
    simp only [poolAt, show ¬ K - j + (572 - q) < K - j by omega, ite_false, Nat.add_sub_cancel_left,
      show 572 - (572 - q) = q by omega]

/-- A heap position's sequence index is unique. -/
theorem poolAt_index_injective (K j : Nat) (hK : K ≤ 286) (hj : j < K) :
    ∀ i i', i < K + j → i' < K + j →
      (if i < K - j then i + 1 else 572 - (i - (K - j))) =
      (if i' < K - j then i' + 1 else 572 - (i' - (K - j))) → i = i' := by
  intro i i' hi hi' heq
  split at heq <;> split at heq <;> omega


/-- Two child stores enlarge the descending tail, while the queue count
loses those two children and gains their fresh parent. -/
theorem poolSum_step (H E : Nat → Nat) (K j n m node : Nat)
    (hK : K ≤ 286) (hj : j + 1 < K)
    (hn : E (572 - 2 * j) = n) (hm : E (571 - 2 * j) = m)
    (hframe : ∀ i < 2 * j, E (572 - i) = H (572 - i))
    (hqueue : ∀ F : Nat → Nat,
      rs (fun i => F (E (i + 1))) (K - j - 1) + F n + F m =
        rs (fun i => F (H (i + 1))) (K - j) + F node)
    (F : Nat → Nat) :
    poolSum E (K - (j + 1)) (2 * (j + 1)) F = poolSum H (K - j) (2 * j) F + F node := by
  have htail : rs (fun i => F (E (572 - i))) (2 * (j + 1)) =
      rs (fun i => F (H (572 - i))) (2 * j) + F n + F m := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, rs_succ, rs_succ]
    rw [rs_congr (fun i hi => congrArg F (hframe i hi)), hn,
      show 572 - (2 * j + 1) = 571 - 2 * j by omega, hm]
  have hq := hqueue F
  unfold poolSum
  rw [htail, show K - (j + 1) = K - j - 1 by omega]
  omega

/-- Exact pool observations imply exact multiplicities. -/
theorem pool_counts (H H0 : Nat → Nat) (len tail K N j : Nat)
    (hsum : ∀ F : Nat → Nat, poolSum H len tail F =
      rs (fun i => F (H0 (i + 1))) K + rs (fun i => F (N + i)) j) (v : Nat) :
    cnt (poolAt H len) (len + tail) v = cnt (fun i => H0 (i + 1)) K v + cnt (fun i => N + i) j v := by
  simpa only [poolSum_eq_rs, cnt] using hsum (fun q => if q = v then 1 else 0)

/-- Initially distinct leaf nodes below N and the distinct internal range
N..N+j have no repeated values in the complete pool. -/
theorem pool_unique (H H0 : Nat → Nat) (len tail K N j : Nat)
    (hinit : ∀ i < K, H0 (i + 1) < N)
    (hinj : ∀ i i', i < K → i' < K → H0 (i + 1) = H0 (i' + 1) → i = i')
    (hsum : ∀ F : Nat → Nat, poolSum H len tail F =
      rs (fun i => F (H0 (i + 1))) K + rs (fun i => F (N + i)) j) :
    ∀ i i', i < len + tail → i' < len + tail → poolAt H len i = poolAt H len i' → i = i' := by
  apply injective_of_counts
  intro v
  rw [pool_counts H H0 len tail K N j hsum v]
  by_cases hv : v < N
  · have hz : cnt (fun i => N + i) j v = 0 := cnt_zero (fun i hi => by omega)
    rw [hz, Nat.add_zero]
    exact cnt_le_one _ _ _ hinj
  · have hz : cnt (fun i => H0 (i + 1)) K v = 0 := cnt_zero (fun i hi => by have := hinit i hi; omega)
    rw [hz, Nat.zero_add]
    exact cnt_le_one _ _ _ (fun i i' hi hi' he => by omega)

/-- Each pool value is either an original leaf or an already created
internal node. This follows from counts, without a membership assumption. -/
theorem pool_origin (H H0 : Nat → Nat) (len tail K N j : Nat)
    (hsum : ∀ F : Nat → Nat, poolSum H len tail F =
      rs (fun i => F (H0 (i + 1))) K + rs (fun i => F (N + i)) j)
    (i : Nat) (hi : i < len + tail) :
    (∃ q < K, H0 (q + 1) = poolAt H len i) ∨ (N ≤ poolAt H len i ∧ poolAt H len i < N + j) := by
  classical
  by_cases hleaf : ∃ q < K, H0 (q + 1) = poolAt H len i
  · exact Or.inl hleaf
  right
  by_cases hint : N ≤ poolAt H len i ∧ poolAt H len i < N + j
  · exact hint
  exfalso
  have hc := cnt_pos (P := poolAt H len) hi rfl
  rw [pool_counts H H0 len tail K N j hsum (poolAt H len i)] at hc
  have hz1 : cnt (fun q => H0 (q + 1)) K (poolAt H len i) = 0 := cnt_zero (fun q hq he => hleaf ⟨q, hq, he⟩)
  have hz2 : cnt (fun q => N + q) j (poolAt H len i) = 0 := cnt_zero (fun q hq he => hint (by omega))
  omega

/-- Every already created internal node occurs in the pool. -/
theorem pool_internal (H H0 : Nat → Nat) (len tail K N j : Nat)
    (hsum : ∀ F : Nat → Nat, poolSum H len tail F =
      rs (fun i => F (H0 (i + 1))) K + rs (fun i => F (N + i)) j)
    (a : Nat) (ha : a < j) : ∃ i < len + tail, poolAt H len i = N + a := by
  apply cnt_exists
  rw [pool_counts H H0 len tail K N j hsum (N + a)]
  have hc := cnt_pos (P := fun i => N + i) ha rfl
  omega

/-- Every active heap position has a bounded sequence index that maps
back to that exact position, independently of the node values. -/
theorem pool_position_preimage (K j q : Nat) (hK : K ≤ 286) (hj : j < K)
    (hq : (1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) :
    ∃ i : Nat, i < K + j ∧ (if i < K - j then i + 1 else 572 - (i - (K - j))) = q := by
  rcases hq with hq | hq
  · refine ⟨q - 1, by omega, ?_⟩
    rw [if_pos (by omega)]
    omega
  · refine ⟨K - j + (572 - q), by omega, ?_⟩
    rw [if_neg (by omega)]
    omega

/-- Distinct sequence values yield distinct active heap positions. -/
theorem pool_heap_injective (H : Nat → Nat) (K j : Nat) (hK : K ≤ 286) (hj : j < K)
    (hinj : ∀ i i', i < K + j → i' < K + j → poolAt H (K - j) i = poolAt H (K - j) i' → i = i') :
    ∀ q q', ((1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) →
      ((1 ≤ q' ∧ q' ≤ K - j) ∨ (573 - 2 * j ≤ q' ∧ q' < 573)) → H q = H q' → q = q' := by
  intro q q' hq hq' heq
  obtain ⟨i, hi, hpos⟩ := pool_position_preimage K j q hK hj hq
  obtain ⟨i', hi', hpos'⟩ := pool_position_preimage K j q' hK hj hq'
  have hval : ∀ k, poolAt H (K - j) k = H (if k < K - j then k + 1 else 572 - (k - (K - j))) := by
    intro k
    unfold poolAt
    split <;> rfl
  have heqi : poolAt H (K - j) i = poolAt H (K - j) i' := by rw [hval, hval, hpos, hpos']; exact heq
  have hii := hinj i i' hi hi' heqi
  rw [hii] at hpos
  omega


/-- Every original leaf remains in the complete pool. -/
theorem pool_leaf (H H0 : Nat → Nat) (len tail K N j : Nat)
    (hsum : ∀ F : Nat → Nat, poolSum H len tail F =
      rs (fun i => F (H0 (i + 1))) K + rs (fun i => F (N + i)) j)
    (a : Nat) (ha : a < K) : ∃ i < len + tail, poolAt H len i = H0 (a + 1) := by
  apply cnt_exists
  rw [pool_counts H H0 len tail K N j hsum (H0 (a + 1))]
  have hc := cnt_pos (P := fun i => H0 (i + 1)) ha rfl
  omega

end Zlib.Trees.Proofs.GB
