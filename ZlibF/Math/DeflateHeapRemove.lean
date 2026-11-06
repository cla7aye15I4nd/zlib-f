import ZlibF.Math.DeflateHeap
import ZlibF.Proof.«trees.c.heap.pqrun»

/-! # Removing a binary-heap root: exact entries and finite sums -/

namespace Zlib.Trees.Proofs

/-- A heap permutation preserves any natural-valued sum of its entries. -/
theorem PermOn.sum {A H : Nat → Int32} {len : Nat} (hp : PermOn A H len) (F : Int32 → Nat) :
    GB.rs (fun i => F (A (i + 1))) len = GB.rs (fun i => F (H (i + 1))) len := by
  obtain ⟨σ, hr, hinj, he⟩ := hp
  let P : Nat → Nat := fun i => σ (i + 1) - 1
  have hP : ∀ i < len, P i < len := by
    intro i hi
    have := hr (i + 1) (by omega) (by omega)
    dsimp only [P]; omega
  have hPi : ∀ i j, i < len → j < len → P i = P j → i = j := by
    intro i j hi hj hij
    have ha := hr (i + 1) (by omega) (by omega)
    have hb := hr (j + 1) (by omega) (by omega)
    have hs : σ (i + 1) = σ (j + 1) := by dsimp only [P] at hij; omega
    have := hinj (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) hs
    omega
  have heq : GB.rs (fun i => F (A (i + 1))) len =
      GB.rs (fun i => (fun j => F (H (j + 1))) (P i)) len := by
    apply GB.rs_congr
    intro i hi
    have ha := hr (i + 1) (by omega) (by omega)
    rw [he (i + 1) (by omega) (by omega)]
    dsimp only [P]
    congr 2
    omega
  rw [heq]
  exact GB.rs_perm P (fun j => F (H (j + 1))) len hP hPi

/-- Removing the root loses exactly that entry, for any natural-valued
observation. This does not assume unique node values. -/
theorem PermOn.removed_sum {A H : Nat → Int32} {len : Nat}
    (hp : PermOn A (Hm H len) (len - 1)) (h2 : 2 ≤ len) (F : Int32 → Nat) :
    GB.rs (fun i => F (A (i + 1))) (len - 1) + F (H 1) =
      GB.rs (fun i => F (H (i + 1))) len := by
  rw [hp.sum F]
  have hm : len - 1 = 1 + (len - 2) := by omega
  have hl : len = (len - 1) + 1 := by omega
  rw [hl, GB.rs_succ]
  rw [show len - 1 + 1 = len by omega]
  rw [hm, GB.rs_split, GB.rs_split]
  simp only [GB.rs_succ, GB.rs_zero, Nat.zero_add, Hm]
  have heq : GB.rs (fun i => F (if 1 + i + 1 = 1 then H len else H (1 + i + 1))) (len - 2) =
      GB.rs (fun i => F (H (1 + i + 1))) (len - 2) := by
    apply GB.rs_congr
    intro i hi
    rw [if_neg (by omega)]
  rw [heq, if_pos trivial]
  omega

/-- Every remaining entry came from a non-root old position. -/
theorem PermOn.removed_origin {A H : Nat → Int32} {len : Nat}
    (hp : PermOn A (Hm H len) (len - 1)) (h2 : 2 ≤ len)
    (q : Nat) (hq1 : 1 ≤ q) (hq2 : q ≤ len - 1) :
    ∃ i : Nat, 2 ≤ i ∧ i ≤ len ∧ A q = H i := by
  obtain ⟨σ, hr, hinj, he⟩ := hp
  have hs := hr q hq1 hq2
  have hv := he q hq1 hq2
  dsimp only [Hm] at hv
  by_cases heq : σ q = 1
  · exact ⟨len, h2, Nat.le_refl _, by simpa [heq] using hv⟩
  · exact ⟨σ q, by omega, by omega, by simpa only [if_neg heq] using hv⟩

/-- Every old non-root entry remains present after deletion and sift-down. -/
theorem PermOn.removed_preimage {A H : Nat → Int32} {len : Nat}
    (hp : PermOn A (Hm H len) (len - 1)) (h2 : 2 ≤ len)
    (i : Nat) (hi1 : 2 ≤ i) (hi2 : i ≤ len) :
    ∃ q : Nat, 1 ≤ q ∧ q ≤ len - 1 ∧ A q = H i := by
  by_cases heq : i = len
  · obtain ⟨q, hq1, hq2, hq⟩ := hp.preimage 1 (by omega) (by omega)
    exact ⟨q, hq1, hq2, by simpa [Hm, heq] using hq⟩
  · obtain ⟨q, hq1, hq2, hq⟩ := hp.preimage i (by omega) (by omega)
    exact ⟨q, hq1, hq2, by simpa only [Hm, if_neg (show i ≠ 1 by omega)] using hq⟩

/-- Root deletion and permutation preserve distinctness and exclude the
removed root from every populated slot. -/
theorem PermOn.removed_injective {A H : Nat → Int32} {len : Nat}
    (hp : PermOn A (Hm H len) (len - 1)) (h2 : 2 ≤ len)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → H i = H j → i = j) :
    (∀ q, 1 ≤ q → q ≤ len - 1 → A q ≠ H 1) ∧
      ∀ q q', 1 ≤ q → q ≤ len - 1 → 1 ≤ q' → q' ≤ len - 1 → A q = A q' → q = q' := by
  have hmap : ∀ i, 1 ≤ i → i ≤ len - 1 → 2 ≤ (if i = 1 then len else i) ∧ (if i = 1 then len else i) ≤ len := by
    intro i hi1 hi2
    split <;> omega
  constructor
  · intro q hq1 hq2 hroot
    obtain ⟨i, hi1, hi2, hqi⟩ := hp.removed_origin h2 q hq1 hq2
    have heq := hinj i 1 (by omega) hi2 (by omega) (by omega) (hqi.symm.trans hroot)
    omega
  · obtain ⟨σ, hr, hσ, he⟩ := hp
    intro q q' hq1 hq2 hq'1 hq'2 hqq
    have hs := hr q hq1 hq2
    have hs' := hr q' hq'1 hq'2
    have ha := hmap (σ q) hs.1 hs.2
    have hb := hmap (σ q') hs'.1 hs'.2
    have hvals : H (if σ q = 1 then len else σ q) = H (if σ q' = 1 then len else σ q') := by
      have hqa := he q hq1 hq2
      have hqb := he q' hq'1 hq'2
      dsimp only [Hm] at hqa hqb
      simpa only [apply_ite] using hqa.symm.trans (hqq.trans hqb)
    have hi := hinj _ _ (by omega) ha.2 (by omega) hb.2 hvals
    have heq : σ q = σ q' := by split at hi <;> split at hi <;> omega
    exact hσ q q' hq1 hq2 hq'1 hq'2 heq

/-- Replacing the root removes its old observation and adds the new one. -/
theorem replace_root_sum (H : Nat → Int32) (node : Int32) (len : Nat) (h1 : 1 ≤ len) (F : Int32 → Nat) :
    GB.rs (fun i => F (if i + 1 = 1 then node else H (i + 1))) len + F (H 1) =
      GB.rs (fun i => F (H (i + 1))) len + F node := by
  have h := GB.rs_upd (F := fun i => F (if i + 1 = 1 then node else H (i + 1)))
    (G := fun i => F (H (i + 1))) (n := len) (k := 0) (by omega) (by
      intro i hi hne
      rw [if_neg (by omega)])
  simpa using h


/-- Reindexing a queue preserves distinctness of its entries. -/
theorem PermOn.injective {A H : Nat → Int32} {len : Nat} (hp : PermOn A H len)
    (hi : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → H i = H j → i = j) :
    ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → A i = A j → i = j := by
  obtain ⟨σ, hr, hs, he⟩ := hp
  intro i j hi1 hi2 hj1 hj2 hij
  apply hs i j hi1 hi2 hj1 hj2
  apply hi _ _ (hr i hi1 hi2).1 (hr i hi1 hi2).2 (hr j hj1 hj2).1 (hr j hj1 hj2).2
  rw [← he i hi1 hi2, ← he j hj1 hj2]
  exact hij

end Zlib.Trees.Proofs
